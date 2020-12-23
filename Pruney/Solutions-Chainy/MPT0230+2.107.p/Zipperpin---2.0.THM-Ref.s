%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eOJvnpiB88

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 277 expanded)
%              Number of leaves         :   29 (  94 expanded)
%              Depth                    :   18
%              Number of atoms          :  647 (2457 expanded)
%              Number of equality atoms :   79 ( 330 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( X16 = X17 )
      | ( X16 = X18 )
      | ( X16 = X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('1',plain,(
    ! [X42: $i,X44: $i,X45: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X42 @ X44 ) @ X45 )
        = ( k1_tarski @ X42 ) )
      | ( X42 != X44 )
      | ( r2_hidden @ X42 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('2',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r2_hidden @ X44 @ X45 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X44 @ X44 ) @ X45 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r2_hidden @ X44 @ X45 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ X45 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('25',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

thf('33',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X42 @ X44 ) @ X43 )
       != ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2 )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

thf('43',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r2_hidden @ X44 @ X45 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X44 ) @ X45 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('52',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['41','55'])).

thf('57',plain,(
    zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    $false ),
    inference('sup-',[status(thm)],['57','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eOJvnpiB88
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:41:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 197 iterations in 0.078s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(d1_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.53       ( ![E:$i]:
% 0.21/0.53         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.53           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, axiom,
% 0.21/0.53    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.53       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.21/0.53          | ((X16) = (X17))
% 0.21/0.53          | ((X16) = (X18))
% 0.21/0.53          | ((X16) = (X19)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(l38_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.53         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X42 : $i, X44 : $i, X45 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ (k2_tarski @ X42 @ X44) @ X45) = (k1_tarski @ X42))
% 0.21/0.53          | ((X42) != (X44))
% 0.21/0.53          | (r2_hidden @ X42 @ X45))),
% 0.21/0.53      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X44 : $i, X45 : $i]:
% 0.21/0.53         ((r2_hidden @ X44 @ X45)
% 0.21/0.53          | ((k4_xboole_0 @ (k2_tarski @ X44 @ X44) @ X45) = (k1_tarski @ X44)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.53  thf(t69_enumset1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.53  thf('3', plain, (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X44 : $i, X45 : $i]:
% 0.21/0.53         ((r2_hidden @ X44 @ X45)
% 0.21/0.53          | ((k4_xboole_0 @ (k1_tarski @ X44) @ X45) = (k1_tarski @ X44)))),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf(t25_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.21/0.53          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_1, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.21/0.53             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf(t28_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))
% 0.21/0.53         = (k1_tarski @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf(t100_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))
% 0.21/0.53         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf(t21_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.21/0.53           = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf(t46_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.53  thf('14', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))
% 0.21/0.53         = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.53        | (r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['4', '15'])).
% 0.21/0.53  thf(t70_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.53  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_3, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.53       ( ![E:$i]:
% 0.21/0.53         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X25 @ X24)
% 0.21/0.53          | ~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.21/0.53          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.21/0.53         (~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.21/0.53          | ~ (r2_hidden @ X25 @ (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.53          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.53        | ~ (zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((((sk_A) = (sk_B))
% 0.21/0.53        | ((sk_A) = (sk_B))
% 0.21/0.53        | ((sk_A) = (sk_C_1))
% 0.21/0.53        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.53        | ((sk_A) = (sk_C_1))
% 0.21/0.53        | ((sk_A) = (sk_B)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.53  thf('24', plain, (((sk_A) != (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf('25', plain, (((sk_A) != (sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.53  thf('26', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.21/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.21/0.53          | (r2_hidden @ X20 @ X24)
% 0.21/0.53          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.53         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.21/0.53          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.21/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.53  thf('32', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X42 @ X43)
% 0.21/0.53          | ((k4_xboole_0 @ (k2_tarski @ X42 @ X44) @ X43) != (k1_tarski @ X42)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_A))
% 0.21/0.53          | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.53  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2)
% 0.21/0.53          | ((k4_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.21/0.53              != (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.21/0.53          | (zip_tseitin_0 @ sk_A @ X0 @ X0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | (zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '40'])).
% 0.21/0.53  thf('42', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X44 : $i, X45 : $i]:
% 0.21/0.53         ((r2_hidden @ X44 @ X45)
% 0.21/0.53          | ((k4_xboole_0 @ (k1_tarski @ X44) @ X45) = (k1_tarski @ X44)))),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_tarski @ sk_A))
% 0.21/0.53          | (r2_hidden @ sk_A @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['42', '43'])).
% 0.21/0.53  thf('45', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ sk_A @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.53  thf(d7_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X0 : $i, X2 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((X0) != (k1_xboole_0))
% 0.21/0.53          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X1 : $i]:
% 0.21/0.53         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.53  thf(t4_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.21/0.53          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.53          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf('54', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['50', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['46', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | (zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '55'])).
% 0.21/0.53  thf('57', plain, ((zip_tseitin_0 @ sk_A @ sk_A @ sk_A @ sk_A)),
% 0.21/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         (((X16) != (X15)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('59', plain,
% 0.21/0.53      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         ~ (zip_tseitin_0 @ X15 @ X17 @ X18 @ X15)),
% 0.21/0.53      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.53  thf('60', plain, ($false), inference('sup-', [status(thm)], ['57', '59'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
