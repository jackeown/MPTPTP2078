%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SmvuyHnnH9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 149 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  544 (1685 expanded)
%              Number of equality atoms :   12 (  62 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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

thf('0',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ X0 ) @ ( sk_B @ X0 ) )
      | ( ( k3_tarski @ X0 )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      = ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_xboole_0
      = ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_orders_1 @ X18 @ ( k1_orders_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( k1_xboole_0
    = ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('24',plain,(
    r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( X13
       != ( k4_orders_2 @ X12 @ X11 ) )
      | ( m2_orders_2 @ X15 @ X12 @ X11 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k4_orders_2 @ X12 @ X11 ) )
      | ( m2_orders_2 @ X15 @ X12 @ X11 )
      | ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
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
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_1 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_orders_1 @ X19 @ ( k1_orders_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X19 @ ( u1_struct_0 @ X20 ) ) @ X21 )
      | ~ ( m2_orders_2 @ X21 @ X20 @ X19 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['49','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SmvuyHnnH9
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 43 iterations in 0.022s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
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
% 0.20/0.47      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d1_xboole_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf(l49_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         ((r1_tarski @ X7 @ (k3_tarski @ X8)) | ~ (r2_hidden @ X7 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X0) | (r1_tarski @ (sk_B @ X0) @ (k3_tarski @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X3 : $i, X5 : $i]:
% 0.20/0.47         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X0)
% 0.20/0.47          | ~ (r1_tarski @ (k3_tarski @ X0) @ (sk_B @ X0))
% 0.20/0.47          | ((k3_tarski @ X0) = (sk_B @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((~ (r1_tarski @ k1_xboole_0 @ (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.20/0.47        | ((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.20/0.47            = (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.20/0.47        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('7', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((((k1_xboole_0) = (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))
% 0.20/0.47        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(fc9_orders_2, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.47         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.47       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X17)
% 0.20/0.47          | ~ (v5_orders_2 @ X17)
% 0.20/0.47          | ~ (v4_orders_2 @ X17)
% 0.20/0.47          | ~ (v3_orders_2 @ X17)
% 0.20/0.47          | (v2_struct_0 @ X17)
% 0.20/0.47          | ~ (m1_orders_1 @ X18 @ (k1_orders_1 @ (u1_struct_0 @ X17)))
% 0.20/0.47          | ~ (v1_xboole_0 @ (k4_orders_2 @ X17 @ X18)))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.20/0.47  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, (((k1_xboole_0) = (sk_B @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('clc', [status(thm)], ['9', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.20/0.47        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('24', plain, ((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
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
% 0.20/0.47      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.20/0.47         (~ (m1_orders_1 @ X11 @ (k1_orders_1 @ (u1_struct_0 @ X12)))
% 0.20/0.47          | ((X13) != (k4_orders_2 @ X12 @ X11))
% 0.20/0.47          | (m2_orders_2 @ X15 @ X12 @ X11)
% 0.20/0.47          | ~ (r2_hidden @ X15 @ X13)
% 0.20/0.47          | ~ (l1_orders_2 @ X12)
% 0.20/0.47          | ~ (v5_orders_2 @ X12)
% 0.20/0.47          | ~ (v4_orders_2 @ X12)
% 0.20/0.47          | ~ (v3_orders_2 @ X12)
% 0.20/0.47          | (v2_struct_0 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X12)
% 0.20/0.47          | ~ (v3_orders_2 @ X12)
% 0.20/0.47          | ~ (v4_orders_2 @ X12)
% 0.20/0.47          | ~ (v5_orders_2 @ X12)
% 0.20/0.47          | ~ (l1_orders_2 @ X12)
% 0.20/0.47          | ~ (r2_hidden @ X15 @ (k4_orders_2 @ X12 @ X11))
% 0.20/0.47          | (m2_orders_2 @ X15 @ X12 @ X11)
% 0.20/0.47          | ~ (m1_orders_1 @ X11 @ (k1_orders_1 @ (u1_struct_0 @ X12))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
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
% 0.20/0.47         ((m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.20/0.47  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_1))
% 0.20/0.47          | (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_1)),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((m1_orders_1 @ sk_B_1 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t79_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.47               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.47         (~ (m1_orders_1 @ X19 @ (k1_orders_1 @ (u1_struct_0 @ X20)))
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ X19 @ (u1_struct_0 @ X20)) @ X21)
% 0.20/0.47          | ~ (m2_orders_2 @ X21 @ X20 @ X19)
% 0.20/0.47          | ~ (l1_orders_2 @ X20)
% 0.20/0.47          | ~ (v5_orders_2 @ X20)
% 0.20/0.47          | ~ (v4_orders_2 @ X20)
% 0.20/0.47          | ~ (v3_orders_2 @ X20)
% 0.20/0.47          | (v2_struct_0 @ X20))),
% 0.20/0.47      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('42', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.47          | (r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.20/0.47  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.47          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      ((r2_hidden @ (k1_funct_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ k1_xboole_0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '46'])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf('49', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.47  thf('50', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf(t7_ordinal1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.47  thf('53', plain,
% 0.20/0.47      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.47  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.47  thf('55', plain, ($false), inference('demod', [status(thm)], ['49', '54'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
