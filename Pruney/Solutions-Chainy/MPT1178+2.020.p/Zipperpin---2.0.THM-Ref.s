%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zo0Y4ONkWB

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 (  91 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  427 ( 931 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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

thf(t78_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) ) @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_orders_1 @ X19 @ ( k1_orders_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ X19 @ ( u1_struct_0 @ X20 ) ) ) @ X20 @ X19 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t78_orders_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ) ),
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
    ( ( v2_struct_0 @ sk_A )
    | ( m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m2_orders_2 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X15
       != ( k4_orders_2 @ X14 @ X13 ) )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( m2_orders_2 @ X16 @ X14 @ X13 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( m2_orders_2 @ X16 @ X14 @ X13 )
      | ( r2_hidden @ X16 @ ( k4_orders_2 @ X14 @ X13 ) )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ ( k4_orders_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('22',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) @ ( k4_orders_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X11 ) @ ( k3_tarski @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('27',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zo0Y4ONkWB
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:27:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 31 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.47  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.47  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
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
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t78_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( m2_orders_2 @
% 0.20/0.47             ( k1_tarski @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) ) @ A @ B ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X19 : $i, X20 : $i]:
% 0.20/0.47         (~ (m1_orders_1 @ X19 @ (k1_orders_1 @ (u1_struct_0 @ X20)))
% 0.20/0.47          | (m2_orders_2 @ 
% 0.20/0.47             (k1_tarski @ (k1_funct_1 @ X19 @ (u1_struct_0 @ X20))) @ X20 @ X19)
% 0.20/0.47          | ~ (l1_orders_2 @ X20)
% 0.20/0.47          | ~ (v5_orders_2 @ X20)
% 0.20/0.47          | ~ (v4_orders_2 @ X20)
% 0.20/0.47          | ~ (v3_orders_2 @ X20)
% 0.20/0.47          | (v2_struct_0 @ X20))),
% 0.20/0.47      inference('cnf', [status(esa)], [t78_orders_2])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47        | (m2_orders_2 @ 
% 0.20/0.47           (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ 
% 0.20/0.47           sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (m2_orders_2 @ 
% 0.20/0.47           (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ 
% 0.20/0.47           sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.47  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((m2_orders_2 @ 
% 0.20/0.47        (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ sk_A @ sk_B)),
% 0.20/0.47      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
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
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         (~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.20/0.47          | ((X15) != (k4_orders_2 @ X14 @ X13))
% 0.20/0.47          | (r2_hidden @ X16 @ X15)
% 0.20/0.47          | ~ (m2_orders_2 @ X16 @ X14 @ X13)
% 0.20/0.47          | ~ (l1_orders_2 @ X14)
% 0.20/0.47          | ~ (v5_orders_2 @ X14)
% 0.20/0.47          | ~ (v4_orders_2 @ X14)
% 0.20/0.47          | ~ (v3_orders_2 @ X14)
% 0.20/0.47          | (v2_struct_0 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X14)
% 0.20/0.47          | ~ (v3_orders_2 @ X14)
% 0.20/0.47          | ~ (v4_orders_2 @ X14)
% 0.20/0.47          | ~ (v5_orders_2 @ X14)
% 0.20/0.47          | ~ (l1_orders_2 @ X14)
% 0.20/0.47          | ~ (m2_orders_2 @ X16 @ X14 @ X13)
% 0.20/0.47          | (r2_hidden @ X16 @ (k4_orders_2 @ X14 @ X13))
% 0.20/0.47          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.47  thf('14', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('16', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.20/0.47  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.47          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((r2_hidden @ (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.47        (k4_orders_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '20'])).
% 0.20/0.47  thf(l1_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X5 : $i, X7 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((r1_tarski @ 
% 0.20/0.47        (k1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))) @ 
% 0.20/0.47        (k4_orders_2 @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf(t95_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         ((r1_tarski @ (k3_tarski @ X11) @ (k3_tarski @ X12))
% 0.20/0.47          | ~ (r1_tarski @ X11 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((r1_tarski @ 
% 0.20/0.47        (k3_tarski @ 
% 0.20/0.47         (k1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))))) @ 
% 0.20/0.47        (k3_tarski @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf(t31_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.47  thf('26', plain, (![X8 : $i]: ((k3_tarski @ (k1_tarski @ X8)) = (X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((r1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))) @ 
% 0.20/0.47        k1_xboole_0)),
% 0.20/0.47      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i]:
% 0.20/0.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.20/0.47           (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.20/0.47        | ((k1_xboole_0)
% 0.20/0.47            = (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('31', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (((k1_xboole_0)
% 0.20/0.47         = (k1_tarski @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.47  thf(t1_boole, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.47  thf('33', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.47  thf(t49_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.47  thf('35', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['32', '35'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
