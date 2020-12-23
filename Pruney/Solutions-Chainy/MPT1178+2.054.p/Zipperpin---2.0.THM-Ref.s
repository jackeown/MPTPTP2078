%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SjbY1CpmEy

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 154 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  487 (1905 expanded)
%              Number of equality atoms :    8 (  68 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t87_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
           != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
             != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_orders_2])).

thf('1',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ? [C: $i] :
          ( m2_orders_2 @ C @ A @ B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m2_orders_2 @ ( sk_C @ X13 @ X12 ) @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_orders_2])).

thf('3',plain,
    ( ( m2_orders_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m2_orders_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m2_orders_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t82_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ~ ( r1_xboole_0 @ C @ D ) ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m2_orders_2 @ X16 @ X15 @ X14 )
      | ~ ( r1_xboole_0 @ X17 @ X16 )
      | ~ ( m2_orders_2 @ X17 @ X15 @ X14 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( r1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    m2_orders_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['8','9'])).

thf('24',plain,(
    m2_orders_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['8','9'])).

thf('25',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( C
                = ( k4_orders_2 @ A @ B ) )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ C )
                <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X8
       != ( k4_orders_2 @ X7 @ X6 ) )
      | ( r2_hidden @ X9 @ X8 )
      | ~ ( m2_orders_2 @ X9 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( m2_orders_2 @ X9 @ X7 @ X6 )
      | ( r2_hidden @ X9 @ ( k4_orders_2 @ X7 @ X6 ) )
      | ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X3 ) @ X4 )
      | ~ ( r2_hidden @ X5 @ X3 )
      | ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('44',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['23','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['22','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SjbY1CpmEy
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 23 iterations in 0.017s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.47  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.47  thf('0', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.47  thf(t87_orders_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(existence_m2_orders_2, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.47         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X12)
% 0.20/0.47          | ~ (v5_orders_2 @ X12)
% 0.20/0.47          | ~ (v4_orders_2 @ X12)
% 0.20/0.47          | ~ (v3_orders_2 @ X12)
% 0.20/0.47          | (v2_struct_0 @ X12)
% 0.20/0.47          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X12)))
% 0.20/0.47          | (m2_orders_2 @ (sk_C @ X13 @ X12) @ X12 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((m2_orders_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((m2_orders_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.20/0.47  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain, ((m2_orders_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.20/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t82_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.47               ( ![D:$i]:
% 0.20/0.47                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.47         (~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X15)))
% 0.20/0.47          | ~ (m2_orders_2 @ X16 @ X15 @ X14)
% 0.20/0.47          | ~ (r1_xboole_0 @ X17 @ X16)
% 0.20/0.47          | ~ (m2_orders_2 @ X17 @ X15 @ X14)
% 0.20/0.47          | ~ (l1_orders_2 @ X15)
% 0.20/0.47          | ~ (v5_orders_2 @ X15)
% 0.20/0.47          | ~ (v4_orders_2 @ X15)
% 0.20/0.47          | ~ (v3_orders_2 @ X15)
% 0.20/0.47          | (v2_struct_0 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.47          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.47          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | ~ (r1_xboole_0 @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '18'])).
% 0.20/0.47  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r1_xboole_0 @ (sk_C @ sk_B @ sk_A) @ X0)
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, (~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '21'])).
% 0.20/0.47  thf('23', plain, ((m2_orders_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.20/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('24', plain, ((m2_orders_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.20/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d17_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.20/0.47               ( ![D:$i]:
% 0.20/0.47                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7)))
% 0.20/0.47          | ((X8) != (k4_orders_2 @ X7 @ X6))
% 0.20/0.47          | (r2_hidden @ X9 @ X8)
% 0.20/0.47          | ~ (m2_orders_2 @ X9 @ X7 @ X6)
% 0.20/0.47          | ~ (l1_orders_2 @ X7)
% 0.20/0.47          | ~ (v5_orders_2 @ X7)
% 0.20/0.47          | ~ (v4_orders_2 @ X7)
% 0.20/0.47          | ~ (v3_orders_2 @ X7)
% 0.20/0.47          | (v2_struct_0 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X7)
% 0.20/0.47          | ~ (v3_orders_2 @ X7)
% 0.20/0.47          | ~ (v4_orders_2 @ X7)
% 0.20/0.47          | ~ (v5_orders_2 @ X7)
% 0.20/0.47          | ~ (l1_orders_2 @ X7)
% 0.20/0.47          | ~ (m2_orders_2 @ X9 @ X7 @ X6)
% 0.20/0.47          | (r2_hidden @ X9 @ (k4_orders_2 @ X7 @ X6))
% 0.20/0.47          | ~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '27'])).
% 0.20/0.47  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.20/0.47  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t56_setfam_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.47       ( r1_tarski @ C @ B ) ))).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k3_tarski @ X3) @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X5 @ X3)
% 0.20/0.47          | (r1_tarski @ X5 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.20/0.47          | (r1_tarski @ X1 @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X1 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('40', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ X1 @ X0)
% 0.20/0.47          | ~ (r2_hidden @ X1 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.47  thf('42', plain, (![X0 : $i]: (r1_tarski @ (sk_C @ sk_B @ sk_A) @ X0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '41'])).
% 0.20/0.47  thf(t3_xboole_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.47  thf('44', plain, (((sk_C @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.47  thf('45', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '44'])).
% 0.20/0.47  thf('46', plain, ($false), inference('demod', [status(thm)], ['22', '45'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
