%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1918+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aozRbEPQGx

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:34 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 153 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  313 (1109 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t16_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ! [C: $i] :
              ( ( m1_yellow_0 @ C @ B )
             => ( m1_yellow_0 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_yellow_0 @ B @ A )
           => ! [C: $i] :
                ( ( m1_yellow_0 @ C @ B )
               => ( m1_yellow_0 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_yellow_6])).

thf('0',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_yellow_0 @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('2',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_yellow_0 @ X2 @ X3 )
      | ( l1_orders_2 @ X2 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_0])).

thf('6',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','8'])).

thf('10',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_yellow_0 @ X0 @ X1 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('12',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('14',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_yellow_0 @ X2 @ X3 )
      | ( l1_orders_2 @ X2 )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_0])).

thf('16',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('18',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13','18'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tarski @ ( u1_orders_2 @ X0 ) @ ( u1_orders_2 @ X1 ) )
      | ( m1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('24',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( m1_yellow_0 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('27',plain,
    ( ( m1_yellow_0 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( m1_yellow_0 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ~ ( r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_yellow_0 @ X0 @ X1 )
      | ( r1_tarski @ ( u1_orders_2 @ X0 ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('32',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_tarski @ ( u1_orders_2 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('35',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_yellow_0 @ X0 @ X1 )
      | ( r1_tarski @ ( u1_orders_2 @ X0 ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('38',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('40',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_orders_2 @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ ( u1_orders_2 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( u1_orders_2 @ sk_C ) @ ( u1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['29','44'])).


%------------------------------------------------------------------------------
