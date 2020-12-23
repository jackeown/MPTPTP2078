%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1579+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MDpSK4ZD6Q

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:49 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   32 (  49 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  215 ( 711 expanded)
%              Number of equality atoms :   17 (  50 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_toler_1_type,type,(
    k1_toler_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_yellow_0_type,type,(
    v4_yellow_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t58_yellow_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ( v4_yellow_0 @ B @ A )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v4_yellow_0 @ C @ A )
                & ( m1_yellow_0 @ C @ A ) )
             => ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ C ) )
               => ( ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) )
                  = ( g1_orders_2 @ ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( ( v4_yellow_0 @ B @ A )
              & ( m1_yellow_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v4_yellow_0 @ C @ A )
                  & ( m1_yellow_0 @ C @ A ) )
               => ( ( ( u1_struct_0 @ B )
                    = ( u1_struct_0 @ C ) )
                 => ( ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) )
                    = ( g1_orders_2 @ ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_yellow_0])).

thf('0',plain,(
    ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
 != ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
 != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_yellow_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d14_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( ( v4_yellow_0 @ B @ A )
          <=> ( ( u1_orders_2 @ B )
              = ( k1_toler_1 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ X1 )
      | ~ ( v4_yellow_0 @ X0 @ X1 )
      | ( ( u1_orders_2 @ X0 )
        = ( k1_toler_1 @ ( u1_orders_2 @ X1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d14_yellow_0])).

thf('5',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_orders_2 @ sk_C )
      = ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v4_yellow_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_yellow_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( u1_orders_2 @ sk_C )
    = ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('10',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ X1 )
      | ~ ( v4_yellow_0 @ X0 @ X1 )
      | ( ( u1_orders_2 @ X0 )
        = ( k1_toler_1 @ ( u1_orders_2 @ X1 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d14_yellow_0])).

thf('12',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( ( u1_orders_2 @ sk_B )
      = ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v4_yellow_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( k1_toler_1 @ ( u1_orders_2 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','15'])).

thf('17',plain,(
    ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
 != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).


%------------------------------------------------------------------------------
