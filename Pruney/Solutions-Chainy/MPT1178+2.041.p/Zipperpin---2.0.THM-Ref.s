%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wKe9UwZbu3

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:25 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 149 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  525 (1821 expanded)
%              Number of equality atoms :   15 (  78 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

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

thf('0',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ~ ( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ( ( k3_tarski @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ~ ( m1_orders_1 @ X4 @ ( k1_orders_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( X6
       != ( k4_orders_2 @ X5 @ X4 ) )
      | ( m2_orders_2 @ X8 @ X5 @ X4 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('21',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_orders_2 @ X5 @ X4 ) )
      | ( m2_orders_2 @ X8 @ X5 @ X4 )
      | ~ ( m1_orders_1 @ X4 @ ( k1_orders_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('32',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_orders_1 @ X12 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m2_orders_2 @ X14 @ X13 @ X12 )
      | ~ ( r1_xboole_0 @ X15 @ X14 )
      | ~ ( m2_orders_2 @ X15 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('42',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['9','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wKe9UwZbu3
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:39:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 85 iterations in 0.041s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.54  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.23/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.23/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.54  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.23/0.54  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.23/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.23/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.23/0.54  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.23/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.54  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.23/0.54  thf(t87_orders_2, conjecture,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i]:
% 0.23/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.54            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.54          ( ![B:$i]:
% 0.23/0.54            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.23/0.54  thf('0', plain,
% 0.23/0.54      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(fc9_orders_2, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.23/0.54         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.54       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      (![X10 : $i, X11 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ X10)
% 0.23/0.54          | ~ (v5_orders_2 @ X10)
% 0.23/0.54          | ~ (v4_orders_2 @ X10)
% 0.23/0.54          | ~ (v3_orders_2 @ X10)
% 0.23/0.54          | (v2_struct_0 @ X10)
% 0.23/0.54          | ~ (m1_orders_1 @ X11 @ (k1_orders_1 @ (u1_struct_0 @ X10)))
% 0.23/0.54          | ~ (v1_xboole_0 @ (k4_orders_2 @ X10 @ X11)))),
% 0.23/0.54      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54        | (v2_struct_0 @ sk_A)
% 0.23/0.54        | ~ (v3_orders_2 @ sk_A)
% 0.23/0.54        | ~ (v4_orders_2 @ sk_A)
% 0.23/0.54        | ~ (v5_orders_2 @ sk_A)
% 0.23/0.54        | ~ (l1_orders_2 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.54  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.23/0.54  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('9', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.23/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.23/0.54  thf(d1_xboole_0, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(t91_orders_1, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.54            ( ![B:$i]:
% 0.23/0.54              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.23/0.54       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.23/0.54            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X16 : $i, X17 : $i]:
% 0.23/0.54         (((X16) = (k1_xboole_0))
% 0.23/0.54          | ~ (r2_hidden @ X16 @ X17)
% 0.23/0.54          | ((k3_tarski @ X17) != (k1_xboole_0)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.54          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54          | ((X0) = (k1_xboole_0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (((X0) = (k1_xboole_0))
% 0.23/0.54          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54        | ((sk_B @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['10', '14'])).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.23/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(d17_orders_2, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.23/0.54               ( ![D:$i]:
% 0.23/0.54                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X4 : $i, X5 : $i, X6 : $i, X8 : $i]:
% 0.23/0.54         (~ (m1_orders_1 @ X4 @ (k1_orders_1 @ (u1_struct_0 @ X5)))
% 0.23/0.54          | ((X6) != (k4_orders_2 @ X5 @ X4))
% 0.23/0.54          | (m2_orders_2 @ X8 @ X5 @ X4)
% 0.23/0.54          | ~ (r2_hidden @ X8 @ X6)
% 0.23/0.54          | ~ (l1_orders_2 @ X5)
% 0.23/0.54          | ~ (v5_orders_2 @ X5)
% 0.23/0.54          | ~ (v4_orders_2 @ X5)
% 0.23/0.54          | ~ (v3_orders_2 @ X5)
% 0.23/0.54          | (v2_struct_0 @ X5))),
% 0.23/0.54      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.23/0.54         ((v2_struct_0 @ X5)
% 0.23/0.54          | ~ (v3_orders_2 @ X5)
% 0.23/0.54          | ~ (v4_orders_2 @ X5)
% 0.23/0.54          | ~ (v5_orders_2 @ X5)
% 0.23/0.54          | ~ (l1_orders_2 @ X5)
% 0.23/0.54          | ~ (r2_hidden @ X8 @ (k4_orders_2 @ X5 @ X4))
% 0.23/0.54          | (m2_orders_2 @ X8 @ X5 @ X4)
% 0.23/0.54          | ~ (m1_orders_1 @ X4 @ (k1_orders_1 @ (u1_struct_0 @ X5))))),
% 0.23/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.23/0.54  thf('22', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.54          | (v2_struct_0 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '21'])).
% 0.23/0.54  thf('23', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('25', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('26', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.23/0.54          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54          | (v2_struct_0 @ sk_A))),
% 0.23/0.54      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.23/0.54  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('29', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54          | (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.23/0.54      inference('clc', [status(thm)], ['27', '28'])).
% 0.23/0.54  thf('30', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.23/0.54      inference('sup-', [status(thm)], ['18', '29'])).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.23/0.54      inference('sup-', [status(thm)], ['18', '29'])).
% 0.23/0.54  thf('32', plain,
% 0.23/0.54      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(t82_orders_2, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.23/0.54               ( ![D:$i]:
% 0.23/0.54                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('33', plain,
% 0.23/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.54         (~ (m1_orders_1 @ X12 @ (k1_orders_1 @ (u1_struct_0 @ X13)))
% 0.23/0.54          | ~ (m2_orders_2 @ X14 @ X13 @ X12)
% 0.23/0.54          | ~ (r1_xboole_0 @ X15 @ X14)
% 0.23/0.54          | ~ (m2_orders_2 @ X15 @ X13 @ X12)
% 0.23/0.54          | ~ (l1_orders_2 @ X13)
% 0.23/0.54          | ~ (v5_orders_2 @ X13)
% 0.23/0.54          | ~ (v4_orders_2 @ X13)
% 0.23/0.54          | ~ (v3_orders_2 @ X13)
% 0.23/0.54          | (v2_struct_0 @ X13))),
% 0.23/0.54      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.23/0.54  thf('34', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((v2_struct_0 @ sk_A)
% 0.23/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.23/0.54          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.23/0.54          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_2))),
% 0.23/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.23/0.54  thf('35', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('36', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('37', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('39', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((v2_struct_0 @ sk_A)
% 0.23/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.23/0.54          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.23/0.54          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_2))),
% 0.23/0.54      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.23/0.54  thf('40', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.23/0.54          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.23/0.54          | (v2_struct_0 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['31', '39'])).
% 0.23/0.54  thf('41', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54        | (v2_struct_0 @ sk_A)
% 0.23/0.54        | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.23/0.54        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['30', '40'])).
% 0.23/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.54  thf('42', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.23/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.54  thf('43', plain,
% 0.23/0.54      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.23/0.54        | (v2_struct_0 @ sk_A)
% 0.23/0.54        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.23/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.23/0.54  thf('44', plain,
% 0.23/0.54      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.23/0.54      inference('simplify', [status(thm)], ['43'])).
% 0.23/0.54  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('46', plain, ((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.23/0.54      inference('clc', [status(thm)], ['44', '45'])).
% 0.23/0.54  thf('47', plain, ($false), inference('demod', [status(thm)], ['9', '46'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
