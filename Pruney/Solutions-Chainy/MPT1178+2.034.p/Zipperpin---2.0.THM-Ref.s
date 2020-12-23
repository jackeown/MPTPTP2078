%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7d2dUqOy2j

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:24 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 136 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  573 (1384 expanded)
%              Number of equality atoms :   11 (  47 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

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
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ ( k3_tarski @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ ( sk_B @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X15
       != ( k4_orders_2 @ X14 @ X13 ) )
      | ( m2_orders_2 @ X17 @ X14 @ X13 )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k4_orders_2 @ X14 @ X13 ) )
      | ( m2_orders_2 @ X17 @ X14 @ X13 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_orders_1 @ X20 @ ( k1_orders_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
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

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_orders_1 @ X21 @ ( k1_orders_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X21 @ ( u1_struct_0 @ X22 ) ) @ X23 )
      | ~ ( m2_orders_2 @ X23 @ X22 @ X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','14'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7d2dUqOy2j
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 234 iterations in 0.189s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.43/0.62  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.43/0.62  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.62  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.43/0.62  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.43/0.62  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.43/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.62  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.43/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.62  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.43/0.62  thf(t87_orders_2, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.43/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.43/0.62            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.43/0.62          ( ![B:$i]:
% 0.43/0.62            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t7_xboole_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.62  thf(d1_xboole_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.62  thf(l49_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i]:
% 0.43/0.62         ((r1_tarski @ X9 @ (k3_tarski @ X10)) | ~ (r2_hidden @ X9 @ X10))),
% 0.43/0.62      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X0) | (r1_tarski @ (sk_B @ X0) @ (k3_tarski @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf(d3_tarski, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X3 @ X4)
% 0.43/0.62          | (r2_hidden @ X3 @ X5)
% 0.43/0.62          | ~ (r1_tarski @ X4 @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X0)
% 0.43/0.62          | (r2_hidden @ X1 @ (k3_tarski @ X0))
% 0.43/0.62          | ~ (r2_hidden @ X1 @ (sk_B @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((sk_B @ X0) = (k1_xboole_0))
% 0.43/0.62          | (r2_hidden @ (sk_B_1 @ (sk_B @ X0)) @ (k3_tarski @ X0))
% 0.43/0.62          | (v1_xboole_0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X0)
% 0.43/0.62          | ((sk_B @ X0) = (k1_xboole_0))
% 0.43/0.62          | ~ (v1_xboole_0 @ (k3_tarski @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.43/0.62        | ((sk_B @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0))
% 0.43/0.62        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '9'])).
% 0.43/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.43/0.62  thf('11', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.43/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.62  thf(t7_ordinal1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X11 : $i, X12 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.62  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['11', '14'])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      ((((sk_B @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0))
% 0.43/0.62        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '15'])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.43/0.62        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.43/0.62        | (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['16', '17'])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.43/0.62        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(d17_orders_2, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.43/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.43/0.62               ( ![D:$i]:
% 0.43/0.62                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.43/0.62         (~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14)))
% 0.43/0.62          | ((X15) != (k4_orders_2 @ X14 @ X13))
% 0.43/0.62          | (m2_orders_2 @ X17 @ X14 @ X13)
% 0.43/0.62          | ~ (r2_hidden @ X17 @ X15)
% 0.43/0.62          | ~ (l1_orders_2 @ X14)
% 0.43/0.62          | ~ (v5_orders_2 @ X14)
% 0.43/0.62          | ~ (v4_orders_2 @ X14)
% 0.43/0.62          | ~ (v3_orders_2 @ X14)
% 0.43/0.62          | (v2_struct_0 @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X14)
% 0.43/0.62          | ~ (v3_orders_2 @ X14)
% 0.43/0.62          | ~ (v4_orders_2 @ X14)
% 0.43/0.62          | ~ (v5_orders_2 @ X14)
% 0.43/0.62          | ~ (l1_orders_2 @ X14)
% 0.43/0.62          | ~ (r2_hidden @ X17 @ (k4_orders_2 @ X14 @ X13))
% 0.43/0.62          | (m2_orders_2 @ X17 @ X14 @ X13)
% 0.43/0.62          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X14))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.43/0.62          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.43/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.43/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.43/0.62          | ~ (v4_orders_2 @ sk_A)
% 0.43/0.62          | ~ (v3_orders_2 @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['20', '22'])).
% 0.43/0.62  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('25', plain, ((v5_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('26', plain, ((v4_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('27', plain, ((v3_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.43/0.62          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.43/0.62  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.43/0.62          | (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.43/0.62      inference('clc', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (((v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.43/0.62        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.43/0.62      inference('sup-', [status(thm)], ['19', '30'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(fc9_orders_2, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.43/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.43/0.62         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.62       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i]:
% 0.43/0.62         (~ (l1_orders_2 @ X19)
% 0.43/0.62          | ~ (v5_orders_2 @ X19)
% 0.43/0.62          | ~ (v4_orders_2 @ X19)
% 0.43/0.62          | ~ (v3_orders_2 @ X19)
% 0.43/0.62          | (v2_struct_0 @ X19)
% 0.43/0.62          | ~ (m1_orders_1 @ X20 @ (k1_orders_1 @ (u1_struct_0 @ X19)))
% 0.43/0.62          | ~ (v1_xboole_0 @ (k4_orders_2 @ X19 @ X20)))),
% 0.43/0.62      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (v3_orders_2 @ sk_A)
% 0.43/0.62        | ~ (v4_orders_2 @ sk_A)
% 0.43/0.62        | ~ (v5_orders_2 @ sk_A)
% 0.43/0.62        | ~ (l1_orders_2 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('35', plain, ((v3_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('36', plain, ((v4_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('37', plain, ((v5_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.43/0.62  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('41', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.43/0.62      inference('clc', [status(thm)], ['39', '40'])).
% 0.43/0.62  thf('42', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 0.43/0.62      inference('sup-', [status(thm)], ['31', '41'])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(t79_orders_2, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.43/0.62         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62           ( ![C:$i]:
% 0.43/0.62             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.43/0.62               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.43/0.62         (~ (m1_orders_1 @ X21 @ (k1_orders_1 @ (u1_struct_0 @ X22)))
% 0.43/0.62          | (r2_hidden @ (k1_funct_1 @ X21 @ (u1_struct_0 @ X22)) @ X23)
% 0.43/0.62          | ~ (m2_orders_2 @ X23 @ X22 @ X21)
% 0.43/0.62          | ~ (l1_orders_2 @ X22)
% 0.43/0.62          | ~ (v5_orders_2 @ X22)
% 0.43/0.62          | ~ (v4_orders_2 @ X22)
% 0.43/0.62          | ~ (v3_orders_2 @ X22)
% 0.43/0.62          | (v2_struct_0 @ X22))),
% 0.43/0.62      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v2_struct_0 @ sk_A)
% 0.43/0.62          | ~ (v3_orders_2 @ sk_A)
% 0.43/0.62          | ~ (v4_orders_2 @ sk_A)
% 0.43/0.62          | ~ (v5_orders_2 @ sk_A)
% 0.43/0.62          | ~ (l1_orders_2 @ sk_A)
% 0.43/0.62          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.43/0.62          | (r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.43/0.62  thf('46', plain, ((v3_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('47', plain, ((v4_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('48', plain, ((v5_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v2_struct_0 @ sk_A)
% 0.43/0.62          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.43/0.62          | (r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.43/0.62  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.43/0.62          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.43/0.62      inference('clc', [status(thm)], ['50', '51'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      ((r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['42', '52'])).
% 0.43/0.62  thf('54', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.62  thf('55', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['11', '14'])).
% 0.43/0.62  thf('57', plain, ($false), inference('demod', [status(thm)], ['55', '56'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
