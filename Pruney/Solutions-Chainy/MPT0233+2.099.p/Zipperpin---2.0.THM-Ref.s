%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0tPPOdcOpr

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 179 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  674 (1433 expanded)
%              Number of equality atoms :   86 ( 187 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( X15 = X16 )
      | ( X15 = X17 )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('3',plain,(
    ! [X54: $i,X56: $i,X57: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X54 @ X56 ) @ X57 )
        = ( k1_tarski @ X54 ) )
      | ( X54 != X56 )
      | ( r2_hidden @ X54 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('4',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r2_hidden @ X56 @ X57 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X56 @ X56 ) @ X57 )
        = ( k1_tarski @ X56 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r2_hidden @ X56 @ X57 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X56 ) @ X57 )
        = ( k1_tarski @ X56 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ( r1_tarski @ X60 @ ( k2_tarski @ X58 @ X61 ) )
      | ( X60
       != ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('8',plain,(
    ! [X58: $i,X61: $i] :
      ( r1_tarski @ ( k1_tarski @ X58 ) @ ( k2_tarski @ X58 @ X61 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','33'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['6','34'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_C )
    | ( sk_A = sk_D )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','40'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_D )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('47',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X54 @ X55 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X54 @ X56 ) @ X55 )
       != ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','43','44'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['49','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2 ) ),
    inference('sup-',[status(thm)],['1','59'])).

thf('61',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    $false ),
    inference('sup-',[status(thm)],['60','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0tPPOdcOpr
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:39:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 285 iterations in 0.103s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.56  thf(d1_enumset1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.56       ( ![E:$i]:
% 0.22/0.56         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.56           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.56  thf(zf_stmt_1, axiom,
% 0.22/0.56    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.56     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.56       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_2, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.56       ( ![E:$i]:
% 0.22/0.56         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.56  thf('0', plain,
% 0.22/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.56         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.22/0.56          | (r2_hidden @ X19 @ X23)
% 0.22/0.56          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.56         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.22/0.56          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.22/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.56  thf('2', plain,
% 0.22/0.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.56         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.22/0.56          | ((X15) = (X16))
% 0.22/0.56          | ((X15) = (X17))
% 0.22/0.56          | ((X15) = (X18)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.56  thf(l38_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.56       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.22/0.56         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (![X54 : $i, X56 : $i, X57 : $i]:
% 0.22/0.56         (((k4_xboole_0 @ (k2_tarski @ X54 @ X56) @ X57) = (k1_tarski @ X54))
% 0.22/0.56          | ((X54) != (X56))
% 0.22/0.56          | (r2_hidden @ X54 @ X57))),
% 0.22/0.56      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (![X56 : $i, X57 : $i]:
% 0.22/0.56         ((r2_hidden @ X56 @ X57)
% 0.22/0.56          | ((k4_xboole_0 @ (k2_tarski @ X56 @ X56) @ X57) = (k1_tarski @ X56)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.56  thf(t69_enumset1, axiom,
% 0.22/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.56  thf('5', plain, (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.22/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      (![X56 : $i, X57 : $i]:
% 0.22/0.56         ((r2_hidden @ X56 @ X57)
% 0.22/0.56          | ((k4_xboole_0 @ (k1_tarski @ X56) @ X57) = (k1_tarski @ X56)))),
% 0.22/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.56  thf(l45_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.22/0.56       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.22/0.56            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      (![X58 : $i, X60 : $i, X61 : $i]:
% 0.22/0.56         ((r1_tarski @ X60 @ (k2_tarski @ X58 @ X61))
% 0.22/0.56          | ((X60) != (k1_tarski @ X58)))),
% 0.22/0.56      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      (![X58 : $i, X61 : $i]:
% 0.22/0.56         (r1_tarski @ (k1_tarski @ X58) @ (k2_tarski @ X58 @ X61))),
% 0.22/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.56  thf(t28_zfmisc_1, conjecture,
% 0.22/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.22/0.56          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_3, negated_conjecture,
% 0.22/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.22/0.56             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.22/0.56  thf('9', plain,
% 0.22/0.56      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.56  thf(t28_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      (![X8 : $i, X9 : $i]:
% 0.22/0.56         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.22/0.56         = (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.56  thf(t18_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.56         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.22/0.56  thf('14', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.56          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['11', '14'])).
% 0.22/0.56  thf('16', plain,
% 0.22/0.56      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.22/0.56      inference('sup-', [status(thm)], ['8', '15'])).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      (![X8 : $i, X9 : $i]:
% 0.22/0.56         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.22/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.22/0.56         = (k1_tarski @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.56  thf(t100_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      (![X3 : $i, X4 : $i]:
% 0.22/0.56         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.56           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.22/0.56         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.56  thf('21', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      (![X3 : $i, X4 : $i]:
% 0.22/0.56         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.56           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.56  thf('23', plain,
% 0.22/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.56  thf(t2_boole, axiom,
% 0.22/0.56    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      (![X3 : $i, X4 : $i]:
% 0.22/0.56         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.56           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.56  thf(t5_boole, axiom,
% 0.22/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.56  thf('27', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.22/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.56  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.56  thf(t48_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      (![X11 : $i, X12 : $i]:
% 0.22/0.56         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.22/0.56           = (k3_xboole_0 @ X11 @ X12))),
% 0.22/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.56  thf('30', plain,
% 0.22/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.56  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.56  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['23', '32'])).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.22/0.56         = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['20', '33'])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.56        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D)))),
% 0.22/0.56      inference('sup+', [status(thm)], ['6', '34'])).
% 0.22/0.56  thf(t70_enumset1, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      (![X27 : $i, X28 : $i]:
% 0.22/0.56         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.22/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X24 @ X23)
% 0.22/0.56          | ~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.22/0.56          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.22/0.56         (~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.22/0.56          | ~ (r2_hidden @ X24 @ (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.56          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['36', '38'])).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.56        | ~ (zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C))),
% 0.22/0.56      inference('sup-', [status(thm)], ['35', '39'])).
% 0.22/0.56  thf('41', plain,
% 0.22/0.56      ((((sk_A) = (sk_C))
% 0.22/0.56        | ((sk_A) = (sk_C))
% 0.22/0.56        | ((sk_A) = (sk_D))
% 0.22/0.56        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['2', '40'])).
% 0.22/0.56  thf('42', plain,
% 0.22/0.56      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.22/0.56        | ((sk_A) = (sk_D))
% 0.22/0.56        | ((sk_A) = (sk_C)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.56  thf('43', plain, (((sk_A) != (sk_C))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.56  thf('44', plain, (((sk_A) != (sk_D))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.56  thf('45', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.56      inference('simplify_reflect-', [status(thm)], ['42', '43', '44'])).
% 0.22/0.56  thf('46', plain,
% 0.22/0.56      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.22/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.56  thf('47', plain,
% 0.22/0.56      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X54 @ X55)
% 0.22/0.56          | ((k4_xboole_0 @ (k2_tarski @ X54 @ X56) @ X55) != (k1_tarski @ X54)))),
% 0.22/0.56      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.22/0.56  thf('48', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.22/0.56          | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.56  thf('49', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_A))
% 0.22/0.56          | ~ (r2_hidden @ sk_A @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['45', '48'])).
% 0.22/0.56  thf('50', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.56  thf('51', plain,
% 0.22/0.56      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.56  thf('52', plain,
% 0.22/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['50', '51'])).
% 0.22/0.56  thf('53', plain,
% 0.22/0.56      (![X3 : $i, X4 : $i]:
% 0.22/0.56         ((k4_xboole_0 @ X3 @ X4)
% 0.22/0.56           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.56  thf('54', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.56           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.56  thf('55', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.22/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.56  thf('56', plain,
% 0.22/0.56      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.56  thf('57', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.22/0.56      inference('simplify_reflect-', [status(thm)], ['42', '43', '44'])).
% 0.22/0.56  thf('58', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_A @ X0))),
% 0.22/0.56      inference('demod', [status(thm)], ['49', '56', '57'])).
% 0.22/0.56  thf('59', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.22/0.56      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.56  thf('60', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]: (zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2)),
% 0.22/0.56      inference('sup-', [status(thm)], ['1', '59'])).
% 0.22/0.56  thf('61', plain,
% 0.22/0.56      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.56         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.56  thf('62', plain,
% 0.22/0.56      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.22/0.56         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 0.22/0.56      inference('simplify', [status(thm)], ['61'])).
% 0.22/0.56  thf('63', plain, ($false), inference('sup-', [status(thm)], ['60', '62'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
