%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T2Cx0df9vT

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 234 expanded)
%              Number of leaves         :   33 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  541 (2805 expanded)
%              Number of equality atoms :   14 ( 107 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_orders_1 @ X19 @ ( k1_orders_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m2_orders_2 @ ( sk_C_1 @ X19 @ X18 ) @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_orders_2])).

thf('2',plain,
    ( ( m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
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
    ( ( m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m2_orders_2 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['7','8'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_orders_1 @ X12 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( X14
       != ( k4_orders_2 @ X13 @ X12 ) )
      | ( r2_hidden @ X15 @ X14 )
      | ~ ( m2_orders_2 @ X15 @ X13 @ X12 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('13',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( m2_orders_2 @ X15 @ X13 @ X12 )
      | ( r2_hidden @ X15 @ ( k4_orders_2 @ X13 @ X12 ) )
      | ~ ( m1_orders_1 @ X12 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ ( k3_tarski @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('24',plain,(
    r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_C_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','30'])).

thf('32',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','30'])).

thf('33',plain,(
    m1_orders_1 @ sk_B_1 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m2_orders_2 @ X22 @ X21 @ X20 )
      | ~ ( r1_xboole_0 @ X23 @ X22 )
      | ~ ( m2_orders_2 @ X23 @ X21 @ X20 )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t82_orders_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('42',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf(t98_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X10 ) @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t98_zfmisc_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('47',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('48',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('49',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('sup-',[status(thm)],['31','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T2Cx0df9vT
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 176 iterations in 0.091s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.55  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.55  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.55  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.55  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.55  thf(t87_orders_2, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.55            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(existence_m2_orders_2, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.55         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X18)
% 0.20/0.55          | ~ (v5_orders_2 @ X18)
% 0.20/0.55          | ~ (v4_orders_2 @ X18)
% 0.20/0.55          | ~ (v3_orders_2 @ X18)
% 0.20/0.55          | (v2_struct_0 @ X18)
% 0.20/0.55          | ~ (m1_orders_1 @ X19 @ (k1_orders_1 @ (u1_struct_0 @ X18)))
% 0.20/0.55          | (m2_orders_2 @ (sk_C_1 @ X19 @ X18) @ X18 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.55        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.55        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.55        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)
% 0.20/0.55        | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.55  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain, ((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.20/0.55      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain, ((m2_orders_2 @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A @ sk_B_1)),
% 0.20/0.55      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d17_orders_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         (~ (m1_orders_1 @ X12 @ (k1_orders_1 @ (u1_struct_0 @ X13)))
% 0.20/0.55          | ((X14) != (k4_orders_2 @ X13 @ X12))
% 0.20/0.55          | (r2_hidden @ X15 @ X14)
% 0.20/0.55          | ~ (m2_orders_2 @ X15 @ X13 @ X12)
% 0.20/0.55          | ~ (l1_orders_2 @ X13)
% 0.20/0.55          | ~ (v5_orders_2 @ X13)
% 0.20/0.55          | ~ (v4_orders_2 @ X13)
% 0.20/0.55          | ~ (v3_orders_2 @ X13)
% 0.20/0.55          | (v2_struct_0 @ X13))),
% 0.20/0.55      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X13)
% 0.20/0.55          | ~ (v3_orders_2 @ X13)
% 0.20/0.55          | ~ (v4_orders_2 @ X13)
% 0.20/0.55          | ~ (v5_orders_2 @ X13)
% 0.20/0.55          | ~ (l1_orders_2 @ X13)
% 0.20/0.55          | ~ (m2_orders_2 @ X15 @ X13 @ X12)
% 0.20/0.55          | (r2_hidden @ X15 @ (k4_orders_2 @ X13 @ X12))
% 0.20/0.55          | ~ (m1_orders_1 @ X12 @ (k1_orders_1 @ (u1_struct_0 @ X13))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.20/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.55          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.55  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('17', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('18', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.20/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.20/0.55  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.55          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '21'])).
% 0.20/0.55  thf(l49_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i]:
% 0.20/0.55         ((r1_tarski @ X8 @ (k3_tarski @ X9)) | ~ (r2_hidden @ X8 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      ((r1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 0.20/0.55        (k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('26', plain, ((r1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A) @ k1_xboole_0)),
% 0.20/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.55  thf('27', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X4 : $i, X6 : $i]:
% 0.20/0.55         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain, (((sk_C_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.55  thf('31', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '30'])).
% 0.20/0.55  thf('32', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '30'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t82_orders_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( m2_orders_2 @ D @ A @ B ) => ( ~( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.55         (~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55          | ~ (m2_orders_2 @ X22 @ X21 @ X20)
% 0.20/0.55          | ~ (r1_xboole_0 @ X23 @ X22)
% 0.20/0.55          | ~ (m2_orders_2 @ X23 @ X21 @ X20)
% 0.20/0.55          | ~ (l1_orders_2 @ X21)
% 0.20/0.55          | ~ (v5_orders_2 @ X21)
% 0.20/0.55          | ~ (v4_orders_2 @ X21)
% 0.20/0.55          | ~ (v3_orders_2 @ X21)
% 0.20/0.55          | (v2_struct_0 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t82_orders_2])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.55          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.55          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('37', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('38', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.55          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.55          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['32', '40'])).
% 0.20/0.55  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.55  thf('42', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.55  thf(t98_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 0.20/0.55       ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ))).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ (k3_tarski @ X10) @ X11)
% 0.20/0.55          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [t98_zfmisc_1])).
% 0.20/0.55  thf(d1_xboole_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ (k3_tarski @ X0) @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['42', '45'])).
% 0.20/0.55  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.20/0.55  thf('47', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.20/0.55  thf('48', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.20/0.55  thf(l13_xboole_0, axiom,
% 0.20/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf('50', plain, (((o_0_0_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '50'])).
% 0.20/0.55  thf('52', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.55      inference('demod', [status(thm)], ['46', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['41', '52'])).
% 0.20/0.55  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('55', plain, (![X0 : $i]: ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)),
% 0.20/0.55      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.55  thf('56', plain, ($false), inference('sup-', [status(thm)], ['31', '55'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
