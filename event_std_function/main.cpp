#include <QCoreApplication>

#include <iostream>
#include <functional>
#include <chrono>

#include "event.hpp"



#include <iostream>

struct MyEmitter : event::emitter<MyEmitter> {
    void do_something() {
        std::cout << "Doing something in emitter" << std::endl;
    }
};


int main2() {
    MyEmitter emitter;
    struct Event {
        int value;
    };
    struct Event2 {
        int value;
    };

    // 注册事件监听器
    emitter.on<Event>([](Event& evt, MyEmitter& em) {
        std::cout << "Received Event with value: " << evt.value << std::endl;
        em.do_something();
    });

    // 覆盖上面的
    emitter.on<Event>([](Event& evt, MyEmitter& em) {
        std::cout << "Received Event with value: " << evt.value << std::endl;
        em.do_something();
    });

    emitter.on<Event2>([](Event2& evt, MyEmitter& em) {
        std::cout << "Received Event2 with value: " << evt.value << std::endl;
        em.do_something();
    });

    // 触发事件
    Event evt{42};
    emitter.publish(evt); // 输出: Received event with value: 42, Doing something in emitter

    Event2 evt2{2};
    emitter.publish(evt2);

    emitter.publish(10);

    // 检查事件是否存在
    std::cout << "Has listeners: " << emitter.contains<Event>() << std::endl; // 输出: Has listeners: 1

    // 删除事件监听器
    emitter.erase<Event>();

    // 检查事件是否存在
    std::cout << "Has listeners: " << emitter.contains<Event>() << std::endl; // 输出: Has listeners: 1


    emitter.publish(evt); // 无输出

    return 0;
}




#include <iostream>


#include "event.hpp"
int main() {
    struct GameEvent {
        int player_id;
        int score;
    };

    event::basic_dispatcher<> dispatcher;

    // 注册监听器
    event::connection conn = dispatcher.sink<GameEvent>().connect([](GameEvent& evt) {
        std::cout << "Player " << evt.player_id << " scored " << evt.score << std::endl;
    });

    // 断开当前连接
    //conn.release();
    {
        auto start =  std::chrono::high_resolution_clock::now();
        // 立即触发事件
        dispatcher.trigger(GameEvent{1, 100}); // 输出: Player 1 scored 100

        auto end = std::chrono::high_resolution_clock::now();
        auto duration = duration_cast<std::chrono::nanoseconds>(end - start);

        std::cout << "Elapsed time: " << duration.count() << " ns\n";
    }
    // 加入事件到队列
    dispatcher.enqueue<GameEvent>(2, 201);
    dispatcher.enqueue<GameEvent>(3, 300);

    // 检查队列大小
    std::cout << "Pending events: " << dispatcher.size<GameEvent>() << std::endl; // 输出: Pending events: 2
    {
        auto start =  std::chrono::high_resolution_clock::now();
        // 处理队列中的事件
        dispatcher.update(); // 输出: Player 2 scored 200, Player 3 scored 300

        auto end = std::chrono::high_resolution_clock::now();
        auto duration = duration_cast<std::chrono::nanoseconds>(end - start);

        std::cout << "Elapsed time: " << duration.count() << " ns\n";
    }

    // 清空队列
    dispatcher.clear();
    std::cout << "Pending events after clear: " << dispatcher.size() << std::endl; // 输出: Pending events after clear: 0

    return 0;
}
