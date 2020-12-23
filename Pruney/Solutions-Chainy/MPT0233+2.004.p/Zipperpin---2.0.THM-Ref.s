%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6y2rU4ynxU

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:37 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 112 expanded)
%              Number of leaves         :   38 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  683 ( 811 expanded)
%              Number of equality atoms :   84 ( 101 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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

thf('0',plain,(
    ! [X77: $i,X79: $i,X80: $i] :
      ( ( r1_tarski @ X79 @ ( k2_tarski @ X77 @ X80 ) )
      | ( X79
       != ( k1_tarski @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('1',plain,(
    ! [X77: $i,X80: $i] :
      ( r1_tarski @ ( k1_tarski @ X77 ) @ ( k2_tarski @ X77 @ X80 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
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
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
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
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
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
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','31'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('34',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('36',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X46: $i] :
      ( ( k2_tarski @ X46 @ X46 )
      = ( k1_tarski @ X46 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('39',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_xboole_0 @ ( k2_tarski @ X38 @ X39 ) @ ( k2_tarski @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('41',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( k2_enumset1 @ X49 @ X49 @ X50 @ X51 )
      = ( k1_enumset1 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('42',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ( k1_enumset1 @ X74 @ X76 @ X75 )
      = ( k1_enumset1 @ X74 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ( k1_enumset1 @ X74 @ X76 @ X75 )
      = ( k1_enumset1 @ X74 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('45',plain,
    ( ( k1_enumset1 @ sk_A @ sk_C @ sk_D_1 )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['37','40','43','44'])).

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

thf('46',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('49',plain,(
    ! [X32: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X36 @ X34 )
      | ( X36 = X35 )
      | ( X36 = X32 )
      | ( X34
       != ( k2_tarski @ X35 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('50',plain,(
    ! [X32: $i,X35: $i,X36: $i] :
      ( ( X36 = X32 )
      | ( X36 = X35 )
      | ~ ( r2_hidden @ X36 @ ( k2_tarski @ X35 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_A )
      | ( X0 = sk_C )
      | ( X0 = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6y2rU4ynxU
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.35/1.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.35/1.57  % Solved by: fo/fo7.sh
% 1.35/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.57  % done 2607 iterations in 1.120s
% 1.35/1.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.35/1.57  % SZS output start Refutation
% 1.35/1.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.35/1.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.35/1.57  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.35/1.57  thf(sk_C_type, type, sk_C: $i).
% 1.35/1.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.35/1.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.35/1.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.35/1.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.35/1.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.35/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.35/1.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.35/1.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.35/1.57  thf(l45_zfmisc_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 1.35/1.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.35/1.57            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.35/1.57  thf('0', plain,
% 1.35/1.57      (![X77 : $i, X79 : $i, X80 : $i]:
% 1.35/1.57         ((r1_tarski @ X79 @ (k2_tarski @ X77 @ X80))
% 1.35/1.57          | ((X79) != (k1_tarski @ X77)))),
% 1.35/1.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.35/1.57  thf('1', plain,
% 1.35/1.57      (![X77 : $i, X80 : $i]:
% 1.35/1.57         (r1_tarski @ (k1_tarski @ X77) @ (k2_tarski @ X77 @ X80))),
% 1.35/1.57      inference('simplify', [status(thm)], ['0'])).
% 1.35/1.57  thf(t28_zfmisc_1, conjecture,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.57     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 1.35/1.57          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 1.35/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.57        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 1.35/1.57             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 1.35/1.57    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 1.35/1.57  thf('2', plain,
% 1.35/1.57      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t28_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.35/1.57  thf('3', plain,
% 1.35/1.57      (![X12 : $i, X13 : $i]:
% 1.35/1.57         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.35/1.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.35/1.57  thf('4', plain,
% 1.35/1.57      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 1.35/1.57         = (k2_tarski @ sk_A @ sk_B))),
% 1.35/1.57      inference('sup-', [status(thm)], ['2', '3'])).
% 1.35/1.57  thf(commutativity_k3_xboole_0, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.35/1.57  thf('5', plain,
% 1.35/1.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.35/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.57  thf(t18_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.35/1.57  thf('6', plain,
% 1.35/1.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.35/1.57         ((r1_tarski @ X9 @ X10)
% 1.35/1.57          | ~ (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.35/1.57  thf('7', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['5', '6'])).
% 1.35/1.57  thf('8', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.35/1.57          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D_1)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['4', '7'])).
% 1.35/1.57  thf('9', plain,
% 1.35/1.57      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 1.35/1.57      inference('sup-', [status(thm)], ['1', '8'])).
% 1.35/1.57  thf('10', plain,
% 1.35/1.57      (![X12 : $i, X13 : $i]:
% 1.35/1.57         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.35/1.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.35/1.57  thf('11', plain,
% 1.35/1.57      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 1.35/1.57         = (k1_tarski @ sk_A))),
% 1.35/1.57      inference('sup-', [status(thm)], ['9', '10'])).
% 1.35/1.57  thf(t100_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]:
% 1.35/1.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.35/1.57  thf('12', plain,
% 1.35/1.57      (![X5 : $i, X6 : $i]:
% 1.35/1.57         ((k4_xboole_0 @ X5 @ X6)
% 1.35/1.57           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.35/1.57  thf('13', plain,
% 1.35/1.57      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 1.35/1.57         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.35/1.57      inference('sup+', [status(thm)], ['11', '12'])).
% 1.35/1.57  thf(t17_xboole_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.35/1.57  thf('14', plain,
% 1.35/1.57      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.35/1.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.35/1.57  thf(t3_xboole_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.35/1.57  thf('15', plain,
% 1.35/1.57      (![X14 : $i]:
% 1.35/1.57         (((X14) = (k1_xboole_0)) | ~ (r1_tarski @ X14 @ k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.35/1.57  thf('16', plain,
% 1.35/1.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['14', '15'])).
% 1.35/1.57  thf('17', plain,
% 1.35/1.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.35/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.57  thf('18', plain,
% 1.35/1.57      (![X5 : $i, X6 : $i]:
% 1.35/1.57         ((k4_xboole_0 @ X5 @ X6)
% 1.35/1.57           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.35/1.57  thf('19', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         ((k4_xboole_0 @ X0 @ X1)
% 1.35/1.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.35/1.57      inference('sup+', [status(thm)], ['17', '18'])).
% 1.35/1.57  thf('20', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.35/1.57      inference('sup+', [status(thm)], ['16', '19'])).
% 1.35/1.57  thf(t5_boole, axiom,
% 1.35/1.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.35/1.58  thf('21', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.35/1.58      inference('cnf', [status(esa)], [t5_boole])).
% 1.35/1.58  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.35/1.58      inference('demod', [status(thm)], ['20', '21'])).
% 1.35/1.58  thf(t48_xboole_1, axiom,
% 1.35/1.58    (![A:$i,B:$i]:
% 1.35/1.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.35/1.58  thf('23', plain,
% 1.35/1.58      (![X15 : $i, X16 : $i]:
% 1.35/1.58         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.35/1.58           = (k3_xboole_0 @ X15 @ X16))),
% 1.35/1.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.35/1.58  thf('24', plain,
% 1.35/1.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.35/1.58      inference('sup+', [status(thm)], ['22', '23'])).
% 1.35/1.58  thf(idempotence_k3_xboole_0, axiom,
% 1.35/1.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.35/1.58  thf('25', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.35/1.58      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.35/1.58  thf('26', plain,
% 1.35/1.58      (![X5 : $i, X6 : $i]:
% 1.35/1.58         ((k4_xboole_0 @ X5 @ X6)
% 1.35/1.58           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.35/1.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.35/1.58  thf('27', plain,
% 1.35/1.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.35/1.58      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.58  thf('28', plain,
% 1.35/1.58      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.35/1.58      inference('sup-', [status(thm)], ['14', '15'])).
% 1.35/1.58  thf('29', plain,
% 1.35/1.58      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.35/1.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.58  thf('30', plain,
% 1.35/1.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.35/1.58      inference('sup+', [status(thm)], ['28', '29'])).
% 1.35/1.58  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.35/1.58      inference('demod', [status(thm)], ['24', '27', '30'])).
% 1.35/1.58  thf('32', plain,
% 1.35/1.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 1.35/1.58         = (k1_xboole_0))),
% 1.35/1.58      inference('demod', [status(thm)], ['13', '31'])).
% 1.35/1.58  thf(t98_xboole_1, axiom,
% 1.35/1.58    (![A:$i,B:$i]:
% 1.35/1.58     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.35/1.58  thf('33', plain,
% 1.35/1.58      (![X18 : $i, X19 : $i]:
% 1.35/1.58         ((k2_xboole_0 @ X18 @ X19)
% 1.35/1.58           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.35/1.58      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.35/1.58  thf('34', plain,
% 1.35/1.58      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ (k1_tarski @ sk_A))
% 1.35/1.58         = (k5_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ k1_xboole_0))),
% 1.35/1.58      inference('sup+', [status(thm)], ['32', '33'])).
% 1.35/1.58  thf(commutativity_k2_xboole_0, axiom,
% 1.35/1.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.35/1.58  thf('35', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.35/1.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.35/1.58  thf('36', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.35/1.58      inference('cnf', [status(esa)], [t5_boole])).
% 1.35/1.58  thf('37', plain,
% 1.35/1.58      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 1.35/1.58         = (k2_tarski @ sk_C @ sk_D_1))),
% 1.35/1.58      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.35/1.58  thf(t69_enumset1, axiom,
% 1.35/1.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.35/1.58  thf('38', plain,
% 1.35/1.58      (![X46 : $i]: ((k2_tarski @ X46 @ X46) = (k1_tarski @ X46))),
% 1.35/1.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.35/1.58  thf(l53_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.58     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.35/1.58       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 1.35/1.58  thf('39', plain,
% 1.35/1.58      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X38 @ X39 @ X40 @ X41)
% 1.35/1.58           = (k2_xboole_0 @ (k2_tarski @ X38 @ X39) @ (k2_tarski @ X40 @ X41)))),
% 1.35/1.58      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.35/1.58  thf('40', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 1.35/1.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 1.35/1.58      inference('sup+', [status(thm)], ['38', '39'])).
% 1.35/1.58  thf(t71_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i]:
% 1.35/1.58     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.35/1.58  thf('41', plain,
% 1.35/1.58      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X49 @ X49 @ X50 @ X51)
% 1.35/1.58           = (k1_enumset1 @ X49 @ X50 @ X51))),
% 1.35/1.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.35/1.58  thf(t98_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i]:
% 1.35/1.58     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 1.35/1.58  thf('42', plain,
% 1.35/1.58      (![X74 : $i, X75 : $i, X76 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X74 @ X76 @ X75) = (k1_enumset1 @ X74 @ X75 @ X76))),
% 1.35/1.58      inference('cnf', [status(esa)], [t98_enumset1])).
% 1.35/1.58  thf('43', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X2 @ X0 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.35/1.58      inference('sup+', [status(thm)], ['41', '42'])).
% 1.35/1.58  thf('44', plain,
% 1.35/1.58      (![X74 : $i, X75 : $i, X76 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X74 @ X76 @ X75) = (k1_enumset1 @ X74 @ X75 @ X76))),
% 1.35/1.58      inference('cnf', [status(esa)], [t98_enumset1])).
% 1.35/1.58  thf('45', plain,
% 1.35/1.58      (((k1_enumset1 @ sk_A @ sk_C @ sk_D_1) = (k2_tarski @ sk_C @ sk_D_1))),
% 1.35/1.58      inference('demod', [status(thm)], ['37', '40', '43', '44'])).
% 1.35/1.58  thf(d1_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.35/1.58       ( ![E:$i]:
% 1.35/1.58         ( ( r2_hidden @ E @ D ) <=>
% 1.35/1.58           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.35/1.58  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.35/1.58  thf(zf_stmt_2, axiom,
% 1.35/1.58    (![E:$i,C:$i,B:$i,A:$i]:
% 1.35/1.58     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.35/1.58       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.35/1.58  thf(zf_stmt_3, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.35/1.58       ( ![E:$i]:
% 1.35/1.58         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.35/1.58  thf('46', plain,
% 1.35/1.58      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.35/1.58         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 1.35/1.58          | (r2_hidden @ X25 @ X29)
% 1.35/1.58          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.35/1.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.35/1.58  thf('47', plain,
% 1.35/1.58      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.35/1.58         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 1.35/1.58          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 1.35/1.58      inference('simplify', [status(thm)], ['46'])).
% 1.35/1.58  thf('48', plain,
% 1.35/1.58      (![X0 : $i]:
% 1.35/1.58         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D_1))
% 1.35/1.58          | (zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_A))),
% 1.35/1.58      inference('sup+', [status(thm)], ['45', '47'])).
% 1.35/1.58  thf(d2_tarski, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i]:
% 1.35/1.58     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.35/1.58       ( ![D:$i]:
% 1.35/1.58         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.35/1.58  thf('49', plain,
% 1.35/1.58      (![X32 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.35/1.58         (~ (r2_hidden @ X36 @ X34)
% 1.35/1.58          | ((X36) = (X35))
% 1.35/1.58          | ((X36) = (X32))
% 1.35/1.58          | ((X34) != (k2_tarski @ X35 @ X32)))),
% 1.35/1.58      inference('cnf', [status(esa)], [d2_tarski])).
% 1.35/1.58  thf('50', plain,
% 1.35/1.58      (![X32 : $i, X35 : $i, X36 : $i]:
% 1.35/1.58         (((X36) = (X32))
% 1.35/1.58          | ((X36) = (X35))
% 1.35/1.58          | ~ (r2_hidden @ X36 @ (k2_tarski @ X35 @ X32)))),
% 1.35/1.58      inference('simplify', [status(thm)], ['49'])).
% 1.35/1.58  thf('51', plain,
% 1.35/1.58      (![X0 : $i]:
% 1.35/1.58         ((zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_A)
% 1.35/1.58          | ((X0) = (sk_C))
% 1.35/1.58          | ((X0) = (sk_D_1)))),
% 1.35/1.58      inference('sup-', [status(thm)], ['48', '50'])).
% 1.35/1.58  thf('52', plain,
% 1.35/1.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.35/1.58         (((X21) != (X20)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 1.35/1.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.35/1.58  thf('53', plain,
% 1.35/1.58      (![X20 : $i, X22 : $i, X23 : $i]:
% 1.35/1.58         ~ (zip_tseitin_0 @ X20 @ X22 @ X23 @ X20)),
% 1.35/1.58      inference('simplify', [status(thm)], ['52'])).
% 1.35/1.58  thf('54', plain, ((((sk_A) = (sk_D_1)) | ((sk_A) = (sk_C)))),
% 1.35/1.58      inference('sup-', [status(thm)], ['51', '53'])).
% 1.35/1.58  thf('55', plain, (((sk_A) != (sk_C))),
% 1.35/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.58  thf('56', plain, (((sk_A) != (sk_D_1))),
% 1.35/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.58  thf('57', plain, ($false),
% 1.35/1.58      inference('simplify_reflect-', [status(thm)], ['54', '55', '56'])).
% 1.35/1.58  
% 1.35/1.58  % SZS output end Refutation
% 1.35/1.58  
% 1.35/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
