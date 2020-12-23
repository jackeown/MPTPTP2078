%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QBNJOQXiYt

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 147 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  516 (1609 expanded)
%              Number of equality atoms :   12 (  60 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( m1_orders_1 @ X10 @ ( k1_orders_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X12
       != ( k4_orders_2 @ X11 @ X10 ) )
      | ( m2_orders_2 @ X14 @ X11 @ X10 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k4_orders_2 @ X11 @ X10 ) )
      | ( m2_orders_2 @ X14 @ X11 @ X10 )
      | ~ ( m1_orders_1 @ X10 @ ( k1_orders_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( m2_orders_2 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ ( k3_tarski @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_orders_1 @ X17 @ ( k1_orders_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22','23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['17','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('35',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_orders_2,axiom,(
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
             => ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_orders_1 @ X18 @ ( k1_orders_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X18 @ ( u1_struct_0 @ X19 ) ) @ X20 )
      | ~ ( m2_orders_2 @ X20 @ X19 @ X18 )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('49',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('50',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('51',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('52',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['48','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QBNJOQXiYt
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 38 iterations in 0.020s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.21/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.21/0.47  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.47  thf(d1_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.47  thf(t87_orders_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.47            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d17_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.21/0.47               ( ![D:$i]:
% 0.21/0.47                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.21/0.47         (~ (m1_orders_1 @ X10 @ (k1_orders_1 @ (u1_struct_0 @ X11)))
% 0.21/0.47          | ((X12) != (k4_orders_2 @ X11 @ X10))
% 0.21/0.47          | (m2_orders_2 @ X14 @ X11 @ X10)
% 0.21/0.47          | ~ (r2_hidden @ X14 @ X12)
% 0.21/0.47          | ~ (l1_orders_2 @ X11)
% 0.21/0.47          | ~ (v5_orders_2 @ X11)
% 0.21/0.47          | ~ (v4_orders_2 @ X11)
% 0.21/0.47          | ~ (v3_orders_2 @ X11)
% 0.21/0.47          | (v2_struct_0 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X14 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X11)
% 0.21/0.47          | ~ (v3_orders_2 @ X11)
% 0.21/0.47          | ~ (v4_orders_2 @ X11)
% 0.21/0.47          | ~ (v5_orders_2 @ X11)
% 0.21/0.47          | ~ (l1_orders_2 @ X11)
% 0.21/0.47          | ~ (r2_hidden @ X14 @ (k4_orders_2 @ X11 @ X10))
% 0.21/0.47          | (m2_orders_2 @ X14 @ X11 @ X10)
% 0.21/0.47          | ~ (m1_orders_1 @ X10 @ (k1_orders_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.47  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.47          | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.21/0.47  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.47          | (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('clc', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.47        | (m2_orders_2 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.47  thf(l49_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         ((r1_tarski @ X8 @ (k3_tarski @ X9)) | ~ (r2_hidden @ X8 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X0) | (r1_tarski @ (sk_B @ X0) @ (k3_tarski @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((r1_tarski @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ k1_xboole_0)
% 0.21/0.47        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['13', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(fc9_orders_2, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.47         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X16 : $i, X17 : $i]:
% 0.21/0.47         (~ (l1_orders_2 @ X16)
% 0.21/0.47          | ~ (v5_orders_2 @ X16)
% 0.21/0.47          | ~ (v4_orders_2 @ X16)
% 0.21/0.47          | ~ (v3_orders_2 @ X16)
% 0.21/0.47          | (v2_struct_0 @ X16)
% 0.21/0.47          | ~ (m1_orders_1 @ X17 @ (k1_orders_1 @ (u1_struct_0 @ X16)))
% 0.21/0.47          | ~ (v1_xboole_0 @ (k4_orders_2 @ X16 @ X17)))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.47        | (v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.47        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.47        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.47        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21', '22', '23', '24'])).
% 0.21/0.47  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('27', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      ((r1_tarski @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) @ k1_xboole_0)),
% 0.21/0.47      inference('clc', [status(thm)], ['17', '27'])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('29', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X4 : $i, X6 : $i]:
% 0.21/0.47         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain, (((sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['28', '31'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.21/0.47        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '32'])).
% 0.21/0.47  thf('34', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.47  thf('35', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.47      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t79_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.47               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.47         (~ (m1_orders_1 @ X18 @ (k1_orders_1 @ (u1_struct_0 @ X19)))
% 0.21/0.47          | (r2_hidden @ (k1_funct_1 @ X18 @ (u1_struct_0 @ X19)) @ X20)
% 0.21/0.47          | ~ (m2_orders_2 @ X20 @ X19 @ X18)
% 0.21/0.47          | ~ (l1_orders_2 @ X19)
% 0.21/0.47          | ~ (v5_orders_2 @ X19)
% 0.21/0.47          | ~ (v4_orders_2 @ X19)
% 0.21/0.47          | ~ (v3_orders_2 @ X19)
% 0.21/0.47          | (v2_struct_0 @ X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.47          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.21/0.47          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.21/0.47  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.21/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('clc', [status(thm)], ['43', '44'])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['35', '45'])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.47  thf('48', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.47  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.21/0.47  thf('49', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.21/0.47  thf('50', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.21/0.47  thf(l13_xboole_0, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf('51', plain,
% 0.21/0.47      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.47  thf('52', plain, (((o_0_0_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.47  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('demod', [status(thm)], ['49', '52'])).
% 0.21/0.47  thf('54', plain, ($false), inference('demod', [status(thm)], ['48', '53'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
