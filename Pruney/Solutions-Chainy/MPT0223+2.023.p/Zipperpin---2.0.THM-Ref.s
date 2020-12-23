%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dnBqvyjRVQ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:33 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 116 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  636 ( 867 expanded)
%              Number of equality atoms :   71 (  99 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('9',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','12'])).

thf('25',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','25'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('30',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('31',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('33',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X37 @ X38 @ X39 ) @ ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('36',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('37',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k2_tarski @ sk_B_1 @ sk_A )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X22 @ X26 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X19 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ~ ( zip_tseitin_0 @ X19 @ X19 @ X20 @ X17 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('49',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ( X32 = X29 )
      | ( X31
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('50',plain,(
    ! [X29: $i,X32: $i] :
      ( ( X32 = X29 )
      | ~ ( r2_hidden @ X32 @ ( k1_tarski @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dnBqvyjRVQ
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:01:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.04/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.21  % Solved by: fo/fo7.sh
% 1.04/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.21  % done 1065 iterations in 0.701s
% 1.04/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.21  % SZS output start Refutation
% 1.04/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.04/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.04/1.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.04/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.04/1.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.04/1.21  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.04/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.21  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.04/1.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.04/1.21  thf(sk_B_type, type, sk_B: $i > $i).
% 1.04/1.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.04/1.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.04/1.21  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.04/1.21  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.04/1.21  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.04/1.21  thf(t18_zfmisc_1, conjecture,
% 1.04/1.21    (![A:$i,B:$i]:
% 1.04/1.21     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.04/1.21         ( k1_tarski @ A ) ) =>
% 1.04/1.21       ( ( A ) = ( B ) ) ))).
% 1.04/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.21    (~( ![A:$i,B:$i]:
% 1.04/1.21        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.04/1.21            ( k1_tarski @ A ) ) =>
% 1.04/1.21          ( ( A ) = ( B ) ) ) )),
% 1.04/1.21    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 1.04/1.21  thf('0', plain,
% 1.04/1.21      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 1.04/1.21         = (k1_tarski @ sk_A))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf(commutativity_k3_xboole_0, axiom,
% 1.04/1.21    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.04/1.21  thf('1', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.04/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.21  thf('2', plain,
% 1.04/1.21      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 1.04/1.21         = (k1_tarski @ sk_A))),
% 1.04/1.21      inference('demod', [status(thm)], ['0', '1'])).
% 1.04/1.21  thf('3', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.04/1.21      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.21  thf(t100_xboole_1, axiom,
% 1.04/1.21    (![A:$i,B:$i]:
% 1.04/1.21     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.04/1.21  thf('4', plain,
% 1.04/1.21      (![X10 : $i, X11 : $i]:
% 1.04/1.21         ((k4_xboole_0 @ X10 @ X11)
% 1.04/1.21           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.04/1.21      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.04/1.21  thf('5', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i]:
% 1.04/1.21         ((k4_xboole_0 @ X0 @ X1)
% 1.04/1.21           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.04/1.21      inference('sup+', [status(thm)], ['3', '4'])).
% 1.04/1.21  thf('6', plain,
% 1.04/1.21      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 1.04/1.21         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.04/1.21      inference('sup+', [status(thm)], ['2', '5'])).
% 1.04/1.21  thf('7', plain,
% 1.04/1.21      (((k3_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 1.04/1.21         = (k1_tarski @ sk_A))),
% 1.04/1.21      inference('demod', [status(thm)], ['0', '1'])).
% 1.04/1.21  thf(l97_xboole_1, axiom,
% 1.04/1.21    (![A:$i,B:$i]:
% 1.04/1.21     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.04/1.21  thf('8', plain,
% 1.04/1.21      (![X8 : $i, X9 : $i]:
% 1.04/1.21         (r1_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9))),
% 1.04/1.21      inference('cnf', [status(esa)], [l97_xboole_1])).
% 1.04/1.21  thf('9', plain,
% 1.04/1.21      ((r1_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.04/1.21        (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 1.04/1.21      inference('sup+', [status(thm)], ['7', '8'])).
% 1.04/1.21  thf(t7_xboole_0, axiom,
% 1.04/1.21    (![A:$i]:
% 1.04/1.21     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.04/1.21          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.04/1.21  thf('10', plain,
% 1.04/1.21      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 1.04/1.21      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.04/1.21  thf(t4_xboole_0, axiom,
% 1.04/1.21    (![A:$i,B:$i]:
% 1.04/1.21     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.04/1.21            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.04/1.21       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.04/1.21            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.04/1.21  thf('11', plain,
% 1.04/1.21      (![X3 : $i, X5 : $i, X6 : $i]:
% 1.04/1.21         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 1.04/1.21          | ~ (r1_xboole_0 @ X3 @ X6))),
% 1.04/1.21      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.04/1.21  thf('12', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i]:
% 1.04/1.21         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.04/1.21      inference('sup-', [status(thm)], ['10', '11'])).
% 1.04/1.21  thf('13', plain,
% 1.04/1.21      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.04/1.21         (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A)))
% 1.04/1.21         = (k1_xboole_0))),
% 1.04/1.21      inference('sup-', [status(thm)], ['9', '12'])).
% 1.04/1.21  thf('14', plain,
% 1.04/1.21      (![X10 : $i, X11 : $i]:
% 1.04/1.21         ((k4_xboole_0 @ X10 @ X11)
% 1.04/1.21           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.04/1.21      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.04/1.21  thf('15', plain,
% 1.04/1.21      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.04/1.21         (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A)))
% 1.04/1.21         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 1.04/1.21      inference('sup+', [status(thm)], ['13', '14'])).
% 1.04/1.21  thf(t5_boole, axiom,
% 1.04/1.21    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.04/1.21  thf('16', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.04/1.21      inference('cnf', [status(esa)], [t5_boole])).
% 1.04/1.21  thf('17', plain,
% 1.04/1.21      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.04/1.21         (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A)))
% 1.04/1.21         = (k1_tarski @ sk_A))),
% 1.04/1.21      inference('demod', [status(thm)], ['15', '16'])).
% 1.04/1.21  thf(t48_xboole_1, axiom,
% 1.04/1.21    (![A:$i,B:$i]:
% 1.04/1.21     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.04/1.21  thf('18', plain,
% 1.04/1.21      (![X12 : $i, X13 : $i]:
% 1.04/1.21         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 1.04/1.21           = (k3_xboole_0 @ X12 @ X13))),
% 1.04/1.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.04/1.21  thf('19', plain,
% 1.04/1.21      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 1.04/1.21         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.04/1.21            (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))))),
% 1.04/1.21      inference('sup+', [status(thm)], ['17', '18'])).
% 1.04/1.21  thf(idempotence_k3_xboole_0, axiom,
% 1.04/1.21    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.04/1.21  thf('20', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.04/1.21      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.04/1.21  thf('21', plain,
% 1.04/1.21      (![X10 : $i, X11 : $i]:
% 1.04/1.21         ((k4_xboole_0 @ X10 @ X11)
% 1.04/1.21           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.04/1.21      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.04/1.21  thf('22', plain,
% 1.04/1.21      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.04/1.21      inference('sup+', [status(thm)], ['20', '21'])).
% 1.04/1.21  thf('23', plain,
% 1.04/1.21      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 1.04/1.21         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.04/1.21            (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))))),
% 1.04/1.21      inference('demod', [status(thm)], ['19', '22'])).
% 1.04/1.21  thf('24', plain,
% 1.04/1.21      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.04/1.21         (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A)))
% 1.04/1.21         = (k1_xboole_0))),
% 1.04/1.21      inference('sup-', [status(thm)], ['9', '12'])).
% 1.04/1.21  thf('25', plain,
% 1.04/1.21      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 1.04/1.21      inference('sup+', [status(thm)], ['23', '24'])).
% 1.04/1.21  thf('26', plain,
% 1.04/1.21      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 1.04/1.21         = (k1_xboole_0))),
% 1.04/1.21      inference('demod', [status(thm)], ['6', '25'])).
% 1.04/1.21  thf(t98_xboole_1, axiom,
% 1.04/1.21    (![A:$i,B:$i]:
% 1.04/1.21     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.04/1.21  thf('27', plain,
% 1.04/1.21      (![X15 : $i, X16 : $i]:
% 1.04/1.21         ((k2_xboole_0 @ X15 @ X16)
% 1.04/1.21           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 1.04/1.21      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.04/1.21  thf('28', plain,
% 1.04/1.21      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 1.04/1.21         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))),
% 1.04/1.21      inference('sup+', [status(thm)], ['26', '27'])).
% 1.04/1.21  thf('29', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.04/1.21      inference('cnf', [status(esa)], [t5_boole])).
% 1.04/1.21  thf('30', plain,
% 1.04/1.21      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 1.04/1.21         = (k1_tarski @ sk_B_1))),
% 1.04/1.21      inference('demod', [status(thm)], ['28', '29'])).
% 1.04/1.21  thf(t69_enumset1, axiom,
% 1.04/1.21    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.04/1.21  thf('31', plain,
% 1.04/1.21      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 1.04/1.21      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.04/1.21  thf(t70_enumset1, axiom,
% 1.04/1.21    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.04/1.21  thf('32', plain,
% 1.04/1.21      (![X42 : $i, X43 : $i]:
% 1.04/1.21         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 1.04/1.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.04/1.21  thf(t46_enumset1, axiom,
% 1.04/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.21     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.04/1.21       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 1.04/1.21  thf('33', plain,
% 1.04/1.21      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.04/1.21         ((k2_enumset1 @ X37 @ X38 @ X39 @ X40)
% 1.04/1.21           = (k2_xboole_0 @ (k1_enumset1 @ X37 @ X38 @ X39) @ (k1_tarski @ X40)))),
% 1.04/1.21      inference('cnf', [status(esa)], [t46_enumset1])).
% 1.04/1.21  thf('34', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.21         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 1.04/1.21           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.04/1.21      inference('sup+', [status(thm)], ['32', '33'])).
% 1.04/1.21  thf('35', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i]:
% 1.04/1.21         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 1.04/1.21           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.04/1.21      inference('sup+', [status(thm)], ['31', '34'])).
% 1.04/1.21  thf(t71_enumset1, axiom,
% 1.04/1.21    (![A:$i,B:$i,C:$i]:
% 1.04/1.21     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.04/1.21  thf('36', plain,
% 1.04/1.21      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.04/1.21         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 1.04/1.21           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 1.04/1.21      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.04/1.21  thf('37', plain,
% 1.04/1.21      (![X42 : $i, X43 : $i]:
% 1.04/1.21         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 1.04/1.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.04/1.21  thf('38', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i]:
% 1.04/1.21         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.04/1.21      inference('sup+', [status(thm)], ['36', '37'])).
% 1.04/1.21  thf('39', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i]:
% 1.04/1.21         ((k2_tarski @ X0 @ X1)
% 1.04/1.21           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.04/1.21      inference('demod', [status(thm)], ['35', '38'])).
% 1.04/1.21  thf('40', plain, (((k2_tarski @ sk_B_1 @ sk_A) = (k1_tarski @ sk_B_1))),
% 1.04/1.21      inference('demod', [status(thm)], ['30', '39'])).
% 1.04/1.21  thf('41', plain,
% 1.04/1.21      (![X42 : $i, X43 : $i]:
% 1.04/1.21         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 1.04/1.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.04/1.21  thf(d1_enumset1, axiom,
% 1.04/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.21     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.04/1.21       ( ![E:$i]:
% 1.04/1.21         ( ( r2_hidden @ E @ D ) <=>
% 1.04/1.21           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.04/1.21  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.04/1.21  thf(zf_stmt_2, axiom,
% 1.04/1.21    (![E:$i,C:$i,B:$i,A:$i]:
% 1.04/1.21     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.04/1.21       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.04/1.21  thf(zf_stmt_3, axiom,
% 1.04/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.04/1.21     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.04/1.21       ( ![E:$i]:
% 1.04/1.21         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.04/1.21  thf('42', plain,
% 1.04/1.21      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.04/1.21         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 1.04/1.21          | (r2_hidden @ X22 @ X26)
% 1.04/1.21          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.04/1.21  thf('43', plain,
% 1.04/1.21      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.04/1.21         ((r2_hidden @ X22 @ (k1_enumset1 @ X25 @ X24 @ X23))
% 1.04/1.21          | (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 1.04/1.21      inference('simplify', [status(thm)], ['42'])).
% 1.04/1.21  thf('44', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.21         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.04/1.21          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.04/1.21      inference('sup+', [status(thm)], ['41', '43'])).
% 1.04/1.21  thf('45', plain,
% 1.04/1.21      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.04/1.21         (((X18) != (X19)) | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X17))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.04/1.21  thf('46', plain,
% 1.04/1.21      (![X17 : $i, X19 : $i, X20 : $i]:
% 1.04/1.21         ~ (zip_tseitin_0 @ X19 @ X19 @ X20 @ X17)),
% 1.04/1.21      inference('simplify', [status(thm)], ['45'])).
% 1.04/1.21  thf('47', plain,
% 1.04/1.21      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 1.04/1.21      inference('sup-', [status(thm)], ['44', '46'])).
% 1.04/1.21  thf('48', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))),
% 1.04/1.21      inference('sup+', [status(thm)], ['40', '47'])).
% 1.04/1.21  thf(d1_tarski, axiom,
% 1.04/1.21    (![A:$i,B:$i]:
% 1.04/1.21     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.04/1.21       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.04/1.21  thf('49', plain,
% 1.04/1.21      (![X29 : $i, X31 : $i, X32 : $i]:
% 1.04/1.21         (~ (r2_hidden @ X32 @ X31)
% 1.04/1.21          | ((X32) = (X29))
% 1.04/1.21          | ((X31) != (k1_tarski @ X29)))),
% 1.04/1.21      inference('cnf', [status(esa)], [d1_tarski])).
% 1.04/1.21  thf('50', plain,
% 1.04/1.21      (![X29 : $i, X32 : $i]:
% 1.04/1.21         (((X32) = (X29)) | ~ (r2_hidden @ X32 @ (k1_tarski @ X29)))),
% 1.04/1.21      inference('simplify', [status(thm)], ['49'])).
% 1.04/1.21  thf('51', plain, (((sk_A) = (sk_B_1))),
% 1.04/1.21      inference('sup-', [status(thm)], ['48', '50'])).
% 1.04/1.21  thf('52', plain, (((sk_A) != (sk_B_1))),
% 1.04/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.21  thf('53', plain, ($false),
% 1.04/1.21      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 1.04/1.21  
% 1.04/1.21  % SZS output end Refutation
% 1.04/1.21  
% 1.04/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
