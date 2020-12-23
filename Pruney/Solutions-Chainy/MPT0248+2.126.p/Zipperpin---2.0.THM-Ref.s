%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7AM2Ip1Gjy

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:36 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 445 expanded)
%              Number of leaves         :   20 ( 116 expanded)
%              Depth                    :   28
%              Number of atoms          :  595 (5599 expanded)
%              Number of equality atoms :  112 (1301 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47
        = ( k1_tarski @ X46 ) )
      | ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ X47 @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('22',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('30',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('33',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('34',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['29','31','35'])).

thf('37',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','36'])).

thf('38',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['26','37'])).

thf('39',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('40',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','40'])).

thf('42',plain,(
    r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['16','41'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('43',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ( X16 = X15 )
      | ( X16 = X12 )
      | ( X14
       != ( k2_tarski @ X15 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('45',plain,(
    ! [X12: $i,X15: $i,X16: $i] :
      ( ( X16 = X12 )
      | ( X16 = X15 )
      | ~ ( r2_hidden @ X16 @ ( k2_tarski @ X15 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('50',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','40'])).

thf('52',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X51: $i,X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X51 @ X53 ) @ X54 )
      | ~ ( r2_hidden @ X53 @ X54 )
      | ~ ( r2_hidden @ X51 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ ( sk_B @ sk_C ) @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['10','54'])).

thf('56',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['42','47'])).

thf('57',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('58',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','40'])).

thf('60',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C )
      = sk_C )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','62'])).

thf('64',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','63'])).

thf('65',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','36'])).

thf('66',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','66'])).

thf('68',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['0','67'])).

thf('69',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','36'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7AM2Ip1Gjy
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.68  % Solved by: fo/fo7.sh
% 0.51/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.68  % done 540 iterations in 0.224s
% 0.51/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.68  % SZS output start Refutation
% 0.51/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.68  thf(t43_zfmisc_1, conjecture,
% 0.51/0.68    (![A:$i,B:$i,C:$i]:
% 0.51/0.68     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.51/0.68          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.51/0.68          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.51/0.68          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.51/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.68        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.51/0.68             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.51/0.68             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.51/0.68             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.51/0.68    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.51/0.68  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.51/0.68  thf('1', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.51/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.51/0.68  thf(t12_xboole_1, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.51/0.68  thf('2', plain,
% 0.51/0.68      (![X7 : $i, X8 : $i]:
% 0.51/0.68         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.51/0.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.68  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.68  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('5', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(t7_xboole_1, axiom,
% 0.51/0.68    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.68  thf('6', plain,
% 0.51/0.68      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.51/0.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.51/0.68  thf('7', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.51/0.68      inference('sup+', [status(thm)], ['5', '6'])).
% 0.51/0.68  thf(l3_zfmisc_1, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.51/0.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.51/0.68  thf('8', plain,
% 0.51/0.68      (![X46 : $i, X47 : $i]:
% 0.51/0.68         (((X47) = (k1_tarski @ X46))
% 0.51/0.68          | ((X47) = (k1_xboole_0))
% 0.51/0.68          | ~ (r1_tarski @ X47 @ (k1_tarski @ X46)))),
% 0.51/0.68      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.51/0.68  thf('9', plain,
% 0.51/0.68      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.68  thf(t7_xboole_0, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.51/0.68          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.51/0.68  thf('10', plain,
% 0.51/0.68      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.51/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.51/0.68  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('12', plain,
% 0.51/0.68      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.51/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.51/0.68  thf(d3_xboole_0, axiom,
% 0.51/0.68    (![A:$i,B:$i,C:$i]:
% 0.51/0.68     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.51/0.68       ( ![D:$i]:
% 0.51/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.51/0.68           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.51/0.68  thf('13', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.51/0.68          | (r2_hidden @ X0 @ X2)
% 0.51/0.68          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.51/0.68      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.51/0.68  thf('14', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.51/0.68         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.51/0.68      inference('simplify', [status(thm)], ['13'])).
% 0.51/0.68  thf('15', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (((X0) = (k1_xboole_0))
% 0.51/0.68          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['12', '14'])).
% 0.51/0.68  thf('16', plain,
% 0.51/0.68      (((r2_hidden @ (sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.51/0.68        | ((sk_C) = (k1_xboole_0)))),
% 0.51/0.68      inference('sup+', [status(thm)], ['11', '15'])).
% 0.51/0.68  thf('17', plain,
% 0.51/0.68      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('18', plain,
% 0.51/0.68      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.51/0.68      inference('split', [status(esa)], ['17'])).
% 0.51/0.68  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('20', plain,
% 0.51/0.68      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.68  thf('21', plain,
% 0.51/0.68      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.51/0.68         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.68      inference('split', [status(esa)], ['17'])).
% 0.51/0.68  thf('22', plain,
% 0.51/0.68      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.51/0.68         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.68  thf('23', plain,
% 0.51/0.68      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['22'])).
% 0.51/0.68  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.68  thf('25', plain,
% 0.51/0.68      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 0.51/0.68         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.68      inference('sup+', [status(thm)], ['23', '24'])).
% 0.51/0.68  thf('26', plain,
% 0.51/0.68      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.68      inference('sup+', [status(thm)], ['19', '25'])).
% 0.51/0.68  thf('27', plain,
% 0.51/0.68      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('28', plain,
% 0.51/0.68      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.51/0.68      inference('split', [status(esa)], ['27'])).
% 0.51/0.68  thf('29', plain,
% 0.51/0.68      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.51/0.68      inference('split', [status(esa)], ['27'])).
% 0.51/0.68  thf('30', plain,
% 0.51/0.68      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('31', plain,
% 0.51/0.68      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.51/0.68      inference('split', [status(esa)], ['30'])).
% 0.51/0.68  thf('32', plain,
% 0.51/0.68      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['22'])).
% 0.51/0.68  thf('33', plain,
% 0.51/0.68      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.51/0.68      inference('split', [status(esa)], ['27'])).
% 0.51/0.68  thf('34', plain,
% 0.51/0.68      ((((sk_B_1) != (sk_B_1)))
% 0.51/0.68         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.51/0.68             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.51/0.68  thf('35', plain,
% 0.51/0.68      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.51/0.68  thf('36', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.51/0.68      inference('sat_resolution*', [status(thm)], ['29', '31', '35'])).
% 0.51/0.68  thf('37', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['28', '36'])).
% 0.51/0.68  thf('38', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.51/0.68      inference('simplify_reflect-', [status(thm)], ['26', '37'])).
% 0.51/0.68  thf('39', plain,
% 0.51/0.68      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.51/0.68      inference('split', [status(esa)], ['17'])).
% 0.51/0.68  thf('40', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.51/0.68      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.51/0.68  thf('41', plain, (((sk_C) != (k1_xboole_0))),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['18', '40'])).
% 0.51/0.68  thf('42', plain, ((r2_hidden @ (sk_B @ sk_C) @ (k1_tarski @ sk_A))),
% 0.51/0.68      inference('simplify_reflect-', [status(thm)], ['16', '41'])).
% 0.51/0.68  thf(t69_enumset1, axiom,
% 0.51/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.68  thf('43', plain,
% 0.51/0.68      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.51/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.68  thf(d2_tarski, axiom,
% 0.51/0.68    (![A:$i,B:$i,C:$i]:
% 0.51/0.68     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.51/0.68       ( ![D:$i]:
% 0.51/0.68         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.51/0.68  thf('44', plain,
% 0.51/0.68      (![X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X16 @ X14)
% 0.51/0.68          | ((X16) = (X15))
% 0.51/0.68          | ((X16) = (X12))
% 0.51/0.68          | ((X14) != (k2_tarski @ X15 @ X12)))),
% 0.51/0.68      inference('cnf', [status(esa)], [d2_tarski])).
% 0.51/0.68  thf('45', plain,
% 0.51/0.68      (![X12 : $i, X15 : $i, X16 : $i]:
% 0.51/0.68         (((X16) = (X12))
% 0.51/0.68          | ((X16) = (X15))
% 0.51/0.68          | ~ (r2_hidden @ X16 @ (k2_tarski @ X15 @ X12)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['44'])).
% 0.51/0.68  thf('46', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['43', '45'])).
% 0.51/0.68  thf('47', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['46'])).
% 0.51/0.68  thf('48', plain, (((sk_B @ sk_C) = (sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['42', '47'])).
% 0.51/0.68  thf('49', plain,
% 0.51/0.68      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.51/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.51/0.68  thf('50', plain, (((r2_hidden @ sk_A @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 0.51/0.68      inference('sup+', [status(thm)], ['48', '49'])).
% 0.51/0.68  thf('51', plain, (((sk_C) != (k1_xboole_0))),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['18', '40'])).
% 0.51/0.68  thf('52', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.51/0.68      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.51/0.68  thf(t38_zfmisc_1, axiom,
% 0.51/0.68    (![A:$i,B:$i,C:$i]:
% 0.51/0.68     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.51/0.68       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.51/0.68  thf('53', plain,
% 0.51/0.68      (![X51 : $i, X53 : $i, X54 : $i]:
% 0.51/0.68         ((r1_tarski @ (k2_tarski @ X51 @ X53) @ X54)
% 0.51/0.68          | ~ (r2_hidden @ X53 @ X54)
% 0.51/0.68          | ~ (r2_hidden @ X51 @ X54))),
% 0.51/0.68      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.51/0.68  thf('54', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ sk_C)
% 0.51/0.68          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C))),
% 0.51/0.68      inference('sup-', [status(thm)], ['52', '53'])).
% 0.51/0.68  thf('55', plain,
% 0.51/0.68      ((((sk_C) = (k1_xboole_0))
% 0.51/0.68        | (r1_tarski @ (k2_tarski @ (sk_B @ sk_C) @ sk_A) @ sk_C))),
% 0.51/0.68      inference('sup-', [status(thm)], ['10', '54'])).
% 0.51/0.68  thf('56', plain, (((sk_B @ sk_C) = (sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['42', '47'])).
% 0.51/0.68  thf('57', plain,
% 0.51/0.68      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.51/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.68  thf('58', plain,
% 0.51/0.68      ((((sk_C) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C))),
% 0.51/0.68      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.51/0.68  thf('59', plain, (((sk_C) != (k1_xboole_0))),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['18', '40'])).
% 0.51/0.68  thf('60', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.51/0.68      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.51/0.68  thf('61', plain,
% 0.51/0.68      (![X7 : $i, X8 : $i]:
% 0.51/0.68         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.51/0.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.68  thf('62', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C) = (sk_C))),
% 0.51/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.51/0.68  thf('63', plain,
% 0.51/0.68      ((((k2_xboole_0 @ sk_B_1 @ sk_C) = (sk_C)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.51/0.68      inference('sup+', [status(thm)], ['9', '62'])).
% 0.51/0.68  thf('64', plain,
% 0.51/0.68      ((((k1_tarski @ sk_A) = (sk_C)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.51/0.68      inference('sup+', [status(thm)], ['4', '63'])).
% 0.51/0.68  thf('65', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['28', '36'])).
% 0.51/0.68  thf('66', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.51/0.68      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.51/0.68  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0))),
% 0.51/0.68      inference('demod', [status(thm)], ['3', '66'])).
% 0.51/0.68  thf('68', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 0.51/0.68      inference('demod', [status(thm)], ['0', '67'])).
% 0.51/0.68  thf('69', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.51/0.68      inference('simpl_trail', [status(thm)], ['28', '36'])).
% 0.51/0.68  thf('70', plain, ($false),
% 0.51/0.68      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.51/0.68  
% 0.51/0.68  % SZS output end Refutation
% 0.51/0.68  
% 0.51/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
