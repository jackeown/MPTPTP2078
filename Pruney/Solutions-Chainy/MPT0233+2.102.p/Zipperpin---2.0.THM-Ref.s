%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfhMu1FY73

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:47 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 114 expanded)
%              Number of leaves         :   36 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  666 ( 821 expanded)
%              Number of equality atoms :   74 (  95 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( X19 = X20 )
      | ( X19 = X21 )
      | ( X19 = X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X65: $i,X66: $i] :
      ( r1_tarski @ ( k1_tarski @ X65 ) @ ( k2_tarski @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','31'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('34',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('38',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X30 @ X31 @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('40',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('41',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k1_enumset1 @ X62 @ X64 @ X63 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_enumset1 @ sk_C @ sk_A @ sk_D )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['36','39','42'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X21 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('51',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['0','54'])).

thf('56',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfhMu1FY73
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 886 iterations in 0.267s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.52/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.52/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(d1_enumset1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.52/0.73       ( ![E:$i]:
% 0.52/0.73         ( ( r2_hidden @ E @ D ) <=>
% 0.52/0.73           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, axiom,
% 0.52/0.73    (![E:$i,C:$i,B:$i,A:$i]:
% 0.52/0.73     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.52/0.73       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.52/0.73  thf('0', plain,
% 0.52/0.73      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.52/0.73          | ((X19) = (X20))
% 0.52/0.73          | ((X19) = (X21))
% 0.52/0.73          | ((X19) = (X22)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(t12_zfmisc_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      (![X65 : $i, X66 : $i]:
% 0.52/0.73         (r1_tarski @ (k1_tarski @ X65) @ (k2_tarski @ X65 @ X66))),
% 0.52/0.73      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.52/0.73  thf(t28_zfmisc_1, conjecture,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.52/0.73          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_1, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.52/0.73             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.73  thf(t28_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.52/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.73  thf('4', plain,
% 0.52/0.73      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.52/0.73         = (k2_tarski @ sk_A @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf(t18_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.52/0.73         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.52/0.73          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['4', '7'])).
% 0.52/0.73  thf('9', plain,
% 0.52/0.73      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.73      inference('sup-', [status(thm)], ['1', '8'])).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (![X10 : $i, X11 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.52/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.73  thf('11', plain,
% 0.52/0.73      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.52/0.73         = (k1_tarski @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf(t100_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (![X3 : $i, X4 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.73  thf('13', plain,
% 0.52/0.73      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.52/0.73         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf(t17_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.52/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.52/0.73  thf(t3_xboole_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X12 : $i]:
% 0.52/0.73         (((X12) = (k1_xboole_0)) | ~ (r1_tarski @ X12 @ k1_xboole_0))),
% 0.52/0.73      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (![X3 : $i, X4 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.52/0.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['17', '18'])).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['16', '19'])).
% 0.52/0.73  thf(t5_boole, axiom,
% 0.52/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.73  thf('21', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.52/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.73  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.73      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.73  thf(t48_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      (![X13 : $i, X14 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.52/0.73           = (k3_xboole_0 @ X13 @ X14))),
% 0.52/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['22', '23'])).
% 0.52/0.73  thf(idempotence_k3_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.52/0.73  thf('25', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.52/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.73  thf('26', plain,
% 0.52/0.73      (![X3 : $i, X4 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X3 @ X4)
% 0.52/0.73           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['25', '26'])).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['28', '29'])).
% 0.52/0.73  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['24', '27', '30'])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.52/0.73         = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['13', '31'])).
% 0.52/0.73  thf(t98_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (![X16 : $i, X17 : $i]:
% 0.52/0.73         ((k2_xboole_0 @ X16 @ X17)
% 0.52/0.73           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_A))
% 0.52/0.73         = (k5_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['32', '33'])).
% 0.52/0.73  thf('35', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.52/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.73  thf('36', plain,
% 0.52/0.73      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_A))
% 0.52/0.73         = (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['34', '35'])).
% 0.52/0.73  thf(t70_enumset1, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      (![X35 : $i, X36 : $i]:
% 0.52/0.73         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.52/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.73  thf(t46_enumset1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.52/0.73       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.52/0.73  thf('38', plain,
% 0.52/0.73      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X30 @ X31 @ X32 @ X33)
% 0.52/0.73           = (k2_xboole_0 @ (k1_enumset1 @ X30 @ X31 @ X32) @ (k1_tarski @ X33)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.52/0.73  thf('39', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.52/0.73           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['37', '38'])).
% 0.52/0.73  thf(t71_enumset1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.52/0.73         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.52/0.73           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.52/0.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.52/0.73  thf(t98_enumset1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.52/0.73         ((k1_enumset1 @ X62 @ X64 @ X63) = (k1_enumset1 @ X62 @ X63 @ X64))),
% 0.52/0.73      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         ((k1_enumset1 @ X2 @ X0 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['40', '41'])).
% 0.52/0.73  thf('43', plain,
% 0.52/0.73      (((k1_enumset1 @ sk_C @ sk_A @ sk_D) = (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.73      inference('demod', [status(thm)], ['36', '39', '42'])).
% 0.52/0.73  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.52/0.73  thf(zf_stmt_3, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.52/0.73       ( ![E:$i]:
% 0.52/0.73         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.52/0.73  thf('44', plain,
% 0.52/0.73      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.52/0.73         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 0.52/0.73          | (r2_hidden @ X23 @ X27)
% 0.52/0.73          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.73  thf('45', plain,
% 0.52/0.73      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.52/0.73         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 0.52/0.73          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 0.52/0.73      inference('simplify', [status(thm)], ['44'])).
% 0.52/0.73  thf('46', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D))
% 0.52/0.73          | (zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C))),
% 0.52/0.73      inference('sup+', [status(thm)], ['43', '45'])).
% 0.52/0.73  thf('47', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.73         (((X19) != (X21)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.52/0.73         ~ (zip_tseitin_0 @ X21 @ X20 @ X21 @ X18)),
% 0.52/0.73      inference('simplify', [status(thm)], ['47'])).
% 0.52/0.73  thf('49', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D))),
% 0.52/0.73      inference('sup-', [status(thm)], ['46', '48'])).
% 0.52/0.73  thf('50', plain,
% 0.52/0.73      (![X35 : $i, X36 : $i]:
% 0.52/0.73         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.52/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.73  thf('51', plain,
% 0.52/0.73      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X28 @ X27)
% 0.52/0.73          | ~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 0.52/0.73          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.73  thf('52', plain,
% 0.52/0.73      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.52/0.73         (~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 0.52/0.73          | ~ (r2_hidden @ X28 @ (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['51'])).
% 0.52/0.73  thf('53', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.52/0.73          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.52/0.73      inference('sup-', [status(thm)], ['50', '52'])).
% 0.52/0.73  thf('54', plain, (~ (zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C)),
% 0.52/0.73      inference('sup-', [status(thm)], ['49', '53'])).
% 0.52/0.73  thf('55', plain,
% 0.52/0.73      ((((sk_A) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_A) = (sk_D)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['0', '54'])).
% 0.52/0.73  thf('56', plain, ((((sk_A) = (sk_D)) | ((sk_A) = (sk_C)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['55'])).
% 0.52/0.73  thf('57', plain, (((sk_A) != (sk_C))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.73  thf('58', plain, (((sk_A) != (sk_D))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.52/0.73  thf('59', plain, ($false),
% 0.52/0.73      inference('simplify_reflect-', [status(thm)], ['56', '57', '58'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
