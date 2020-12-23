%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Kh0GlZrUa

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:26 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 156 expanded)
%              Number of leaves         :   27 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  546 (1964 expanded)
%              Number of equality atoms :    7 (  67 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_orders_1 @ X21 @ ( k1_orders_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m2_orders_2 @ ( sk_C_2 @ X21 @ X20 ) @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_orders_2])).

thf('2',plain,
    ( ( m2_orders_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A @ sk_B )
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
    ( ( m2_orders_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m2_orders_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m2_orders_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_orders_1 @ X22 @ ( k1_orders_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m2_orders_2 @ X24 @ X23 @ X22 )
      | ~ ( r1_xboole_0 @ X25 @ X24 )
      | ~ ( m2_orders_2 @ X25 @ X23 @ X22 )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
      | ~ ( r1_xboole_0 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m2_orders_2 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( X16
       != ( k4_orders_2 @ X15 @ X14 ) )
      | ( r2_hidden @ X17 @ X16 )
      | ~ ( m2_orders_2 @ X17 @ X15 @ X14 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( m2_orders_2 @ X17 @ X15 @ X14 )
      | ( r2_hidden @ X17 @ ( k4_orders_2 @ X15 @ X14 ) )
      | ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k3_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B ) ) )
      | ( r1_xboole_0 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['21','45'])).

thf('47',plain,(
    $false ),
    inference('sup-',[status(thm)],['9','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Kh0GlZrUa
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.58  % Solved by: fo/fo7.sh
% 0.42/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.58  % done 221 iterations in 0.115s
% 0.42/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.58  % SZS output start Refutation
% 0.42/0.58  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.42/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.58  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.42/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.42/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.58  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.42/0.58  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.42/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.58  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.42/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.42/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.58  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.42/0.58  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.42/0.58  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.42/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.58  thf(t87_orders_2, conjecture,
% 0.42/0.58    (![A:$i]:
% 0.42/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.42/0.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.42/0.58       ( ![B:$i]:
% 0.42/0.58         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.58           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.42/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.58    (~( ![A:$i]:
% 0.42/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.42/0.58            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.42/0.58          ( ![B:$i]:
% 0.42/0.58            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.58              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.42/0.58    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.42/0.58  thf('0', plain,
% 0.42/0.58      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf(existence_m2_orders_2, axiom,
% 0.42/0.58    (![A:$i,B:$i]:
% 0.42/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.42/0.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.42/0.58         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.58       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.42/0.58  thf('1', plain,
% 0.42/0.58      (![X20 : $i, X21 : $i]:
% 0.42/0.58         (~ (l1_orders_2 @ X20)
% 0.42/0.58          | ~ (v5_orders_2 @ X20)
% 0.42/0.58          | ~ (v4_orders_2 @ X20)
% 0.42/0.58          | ~ (v3_orders_2 @ X20)
% 0.42/0.58          | (v2_struct_0 @ X20)
% 0.42/0.58          | ~ (m1_orders_1 @ X21 @ (k1_orders_1 @ (u1_struct_0 @ X20)))
% 0.42/0.58          | (m2_orders_2 @ (sk_C_2 @ X21 @ X20) @ X20 @ X21))),
% 0.42/0.58      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.42/0.58  thf('2', plain,
% 0.42/0.58      (((m2_orders_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.42/0.58        | (v2_struct_0 @ sk_A)
% 0.42/0.58        | ~ (v3_orders_2 @ sk_A)
% 0.42/0.58        | ~ (v4_orders_2 @ sk_A)
% 0.42/0.58        | ~ (v5_orders_2 @ sk_A)
% 0.42/0.58        | ~ (l1_orders_2 @ sk_A))),
% 0.42/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.58  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('7', plain,
% 0.42/0.58      (((m2_orders_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.42/0.58        | (v2_struct_0 @ sk_A))),
% 0.42/0.58      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.42/0.58  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('9', plain, ((m2_orders_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.42/0.58      inference('clc', [status(thm)], ['7', '8'])).
% 0.42/0.58  thf('10', plain, ((m2_orders_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.42/0.58      inference('clc', [status(thm)], ['7', '8'])).
% 0.42/0.58  thf('11', plain,
% 0.42/0.58      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf(t82_orders_2, axiom,
% 0.42/0.58    (![A:$i]:
% 0.42/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.42/0.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.42/0.58       ( ![B:$i]:
% 0.42/0.58         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.58           ( ![C:$i]:
% 0.42/0.58             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.42/0.58               ( ![D:$i]:
% 0.42/0.58                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.42/0.58  thf('12', plain,
% 0.42/0.58      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.42/0.58         (~ (m1_orders_1 @ X22 @ (k1_orders_1 @ (u1_struct_0 @ X23)))
% 0.42/0.58          | ~ (m2_orders_2 @ X24 @ X23 @ X22)
% 0.42/0.58          | ~ (r1_xboole_0 @ X25 @ X24)
% 0.42/0.58          | ~ (m2_orders_2 @ X25 @ X23 @ X22)
% 0.42/0.58          | ~ (l1_orders_2 @ X23)
% 0.42/0.58          | ~ (v5_orders_2 @ X23)
% 0.42/0.58          | ~ (v4_orders_2 @ X23)
% 0.42/0.58          | ~ (v3_orders_2 @ X23)
% 0.42/0.58          | (v2_struct_0 @ X23))),
% 0.42/0.58      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.42/0.58  thf('13', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((v2_struct_0 @ sk_A)
% 0.42/0.58          | ~ (v3_orders_2 @ sk_A)
% 0.42/0.58          | ~ (v4_orders_2 @ sk_A)
% 0.42/0.58          | ~ (v5_orders_2 @ sk_A)
% 0.42/0.58          | ~ (l1_orders_2 @ sk_A)
% 0.42/0.58          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.42/0.58          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.42/0.58          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.42/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.58  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('18', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((v2_struct_0 @ sk_A)
% 0.42/0.58          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.42/0.58          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.42/0.58          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 0.42/0.58      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.42/0.58  thf('19', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.42/0.58          | ~ (r1_xboole_0 @ (sk_C_2 @ sk_B @ sk_A) @ X0)
% 0.42/0.58          | (v2_struct_0 @ sk_A))),
% 0.42/0.58      inference('sup-', [status(thm)], ['10', '18'])).
% 0.42/0.58  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('21', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         (~ (r1_xboole_0 @ (sk_C_2 @ sk_B @ sk_A) @ X0)
% 0.42/0.58          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.42/0.58      inference('clc', [status(thm)], ['19', '20'])).
% 0.42/0.58  thf('22', plain, ((m2_orders_2 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.42/0.58      inference('clc', [status(thm)], ['7', '8'])).
% 0.42/0.58  thf('23', plain,
% 0.42/0.58      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf(d17_orders_2, axiom,
% 0.42/0.58    (![A:$i]:
% 0.42/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.42/0.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.42/0.58       ( ![B:$i]:
% 0.42/0.58         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.58           ( ![C:$i]:
% 0.42/0.58             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.42/0.58               ( ![D:$i]:
% 0.42/0.58                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.42/0.58  thf('24', plain,
% 0.42/0.58      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.58         (~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X15)))
% 0.42/0.58          | ((X16) != (k4_orders_2 @ X15 @ X14))
% 0.42/0.58          | (r2_hidden @ X17 @ X16)
% 0.42/0.58          | ~ (m2_orders_2 @ X17 @ X15 @ X14)
% 0.42/0.58          | ~ (l1_orders_2 @ X15)
% 0.42/0.58          | ~ (v5_orders_2 @ X15)
% 0.42/0.58          | ~ (v4_orders_2 @ X15)
% 0.42/0.58          | ~ (v3_orders_2 @ X15)
% 0.42/0.58          | (v2_struct_0 @ X15))),
% 0.42/0.58      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.42/0.58  thf('25', plain,
% 0.42/0.58      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.42/0.58         ((v2_struct_0 @ X15)
% 0.42/0.58          | ~ (v3_orders_2 @ X15)
% 0.42/0.58          | ~ (v4_orders_2 @ X15)
% 0.42/0.58          | ~ (v5_orders_2 @ X15)
% 0.42/0.58          | ~ (l1_orders_2 @ X15)
% 0.42/0.58          | ~ (m2_orders_2 @ X17 @ X15 @ X14)
% 0.42/0.58          | (r2_hidden @ X17 @ (k4_orders_2 @ X15 @ X14))
% 0.42/0.58          | ~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X15))))),
% 0.42/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.58  thf('26', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.42/0.58          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.42/0.58          | ~ (l1_orders_2 @ sk_A)
% 0.42/0.58          | ~ (v5_orders_2 @ sk_A)
% 0.42/0.58          | ~ (v4_orders_2 @ sk_A)
% 0.42/0.58          | ~ (v3_orders_2 @ sk_A)
% 0.42/0.58          | (v2_struct_0 @ sk_A))),
% 0.42/0.58      inference('sup-', [status(thm)], ['23', '25'])).
% 0.42/0.58  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('28', plain, ((v5_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('29', plain, ((v4_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('30', plain, ((v3_orders_2 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('31', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.42/0.58          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.42/0.58          | (v2_struct_0 @ sk_A))),
% 0.42/0.58      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.42/0.58  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('33', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.42/0.58          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.42/0.58      inference('clc', [status(thm)], ['31', '32'])).
% 0.42/0.58  thf('34', plain,
% 0.42/0.58      ((r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B))),
% 0.42/0.58      inference('sup-', [status(thm)], ['22', '33'])).
% 0.42/0.58  thf(t3_xboole_0, axiom,
% 0.42/0.58    (![A:$i,B:$i]:
% 0.42/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.42/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.42/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.42/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.42/0.58  thf('35', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.42/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.58  thf(d4_tarski, axiom,
% 0.42/0.58    (![A:$i,B:$i]:
% 0.42/0.58     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.42/0.58       ( ![C:$i]:
% 0.42/0.58         ( ( r2_hidden @ C @ B ) <=>
% 0.42/0.58           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.42/0.58  thf('36', plain,
% 0.42/0.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.58         (~ (r2_hidden @ X5 @ X6)
% 0.42/0.58          | ~ (r2_hidden @ X7 @ X5)
% 0.42/0.58          | (r2_hidden @ X7 @ X8)
% 0.42/0.58          | ((X8) != (k3_tarski @ X6)))),
% 0.42/0.58      inference('cnf', [status(esa)], [d4_tarski])).
% 0.42/0.58  thf('37', plain,
% 0.42/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.58         ((r2_hidden @ X7 @ (k3_tarski @ X6))
% 0.42/0.58          | ~ (r2_hidden @ X7 @ X5)
% 0.42/0.58          | ~ (r2_hidden @ X5 @ X6))),
% 0.42/0.58      inference('simplify', [status(thm)], ['36'])).
% 0.42/0.58  thf('38', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.58         ((r1_xboole_0 @ X0 @ X1)
% 0.42/0.58          | ~ (r2_hidden @ X0 @ X2)
% 0.42/0.58          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['35', '37'])).
% 0.42/0.58  thf('39', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         ((r2_hidden @ (sk_C @ X0 @ (sk_C_2 @ sk_B @ sk_A)) @ 
% 0.42/0.58           (k3_tarski @ (k4_orders_2 @ sk_A @ sk_B)))
% 0.42/0.58          | (r1_xboole_0 @ (sk_C_2 @ sk_B @ sk_A) @ X0))),
% 0.42/0.58      inference('sup-', [status(thm)], ['34', '38'])).
% 0.42/0.58  thf('40', plain,
% 0.42/0.58      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.42/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.58  thf('41', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         ((r2_hidden @ (sk_C @ X0 @ (sk_C_2 @ sk_B @ sk_A)) @ k1_xboole_0)
% 0.42/0.58          | (r1_xboole_0 @ (sk_C_2 @ sk_B @ sk_A) @ X0))),
% 0.42/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.58  thf(t7_ordinal1, axiom,
% 0.42/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.58  thf('42', plain,
% 0.42/0.58      (![X12 : $i, X13 : $i]:
% 0.42/0.58         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.42/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.58  thf('43', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         ((r1_xboole_0 @ (sk_C_2 @ sk_B @ sk_A) @ X0)
% 0.42/0.58          | ~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ (sk_C_2 @ sk_B @ sk_A))))),
% 0.42/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.58  thf('44', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.42/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.58  thf('45', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_2 @ sk_B @ sk_A) @ X0)),
% 0.42/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.42/0.58  thf('46', plain, (![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)),
% 0.42/0.58      inference('demod', [status(thm)], ['21', '45'])).
% 0.42/0.58  thf('47', plain, ($false), inference('sup-', [status(thm)], ['9', '46'])).
% 0.42/0.58  
% 0.42/0.58  % SZS output end Refutation
% 0.42/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
