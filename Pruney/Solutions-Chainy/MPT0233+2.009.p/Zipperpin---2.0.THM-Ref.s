%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mFo9g1XL8P

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:38 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 387 expanded)
%              Number of leaves         :   39 ( 143 expanded)
%              Depth                    :   24
%              Number of atoms          : 1258 (3135 expanded)
%              Number of equality atoms :  133 ( 342 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( X21 = X22 )
      | ( X21 = X23 )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X74: $i,X76: $i,X77: $i] :
      ( ( r1_tarski @ X76 @ ( k2_tarski @ X74 @ X77 ) )
      | ( X76
       != ( k1_tarski @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('2',plain,(
    ! [X74: $i,X77: $i] :
      ( r1_tarski @ ( k1_tarski @ X74 ) @ ( k2_tarski @ X74 @ X77 ) ) ),
    inference(simplify,[status(thm)],['1'])).

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

thf('3',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','28','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','32'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('38',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('40',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_enumset1 @ sk_A @ sk_C @ sk_C @ sk_D )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X74: $i,X76: $i,X77: $i] :
      ( ( r1_tarski @ X76 @ ( k2_tarski @ X74 @ X77 ) )
      | ( X76
       != ( k1_tarski @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('48',plain,(
    ! [X74: $i,X77: $i] :
      ( r1_tarski @ ( k1_tarski @ X77 ) @ ( k2_tarski @ X74 @ X77 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('50',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k2_tarski @ sk_C @ sk_D ) )
      = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','28','31'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['57','72'])).

thf('74',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_B ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['43','73'])).

thf('75',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('76',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X39 @ X40 @ X41 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('78',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('79',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X34 @ X33 @ X32 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('81',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( k1_enumset1 @ X71 @ X73 @ X72 )
      = ( k1_enumset1 @ X71 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('82',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X34 @ X33 @ X32 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( k1_enumset1 @ X71 @ X73 @ X72 )
      = ( k1_enumset1 @ X71 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('85',plain,
    ( ( k1_enumset1 @ sk_C @ sk_D @ sk_B )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['74','77','80','83','84'])).

thf('86',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('92',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( k1_enumset1 @ X71 @ X73 @ X72 )
      = ( k1_enumset1 @ X71 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_C @ sk_D )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('95',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ sk_C @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_C @ sk_D )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('99',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_C @ sk_D )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( k1_enumset1 @ sk_A @ sk_C @ sk_D )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['42','101'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('103',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('104',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['102','104'])).

thf('106',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('107',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('108',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C )
      | ( X0 = sk_C )
      | ( X0 = sk_D )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A )
      | ( X0 = sk_D )
      | ( X0 = sk_C ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('117',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['115','116','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mFo9g1XL8P
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:33:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.76/2.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.76/2.00  % Solved by: fo/fo7.sh
% 1.76/2.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.76/2.00  % done 2662 iterations in 1.541s
% 1.76/2.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.76/2.00  % SZS output start Refutation
% 1.76/2.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.76/2.00  thf(sk_B_type, type, sk_B: $i).
% 1.76/2.00  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.76/2.00  thf(sk_D_type, type, sk_D: $i).
% 1.76/2.00  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.76/2.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.76/2.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.76/2.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.76/2.00  thf(sk_A_type, type, sk_A: $i).
% 1.76/2.00  thf(sk_C_type, type, sk_C: $i).
% 1.76/2.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.76/2.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.76/2.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.76/2.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.76/2.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.76/2.00  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.76/2.00  thf(d1_enumset1, axiom,
% 1.76/2.00    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/2.00     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.76/2.00       ( ![E:$i]:
% 1.76/2.00         ( ( r2_hidden @ E @ D ) <=>
% 1.76/2.00           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.76/2.00  thf(zf_stmt_0, axiom,
% 1.76/2.00    (![E:$i,C:$i,B:$i,A:$i]:
% 1.76/2.00     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.76/2.00       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.76/2.00  thf('0', plain,
% 1.76/2.00      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.76/2.00         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 1.76/2.00          | ((X21) = (X22))
% 1.76/2.00          | ((X21) = (X23))
% 1.76/2.00          | ((X21) = (X24)))),
% 1.76/2.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/2.00  thf(l45_zfmisc_1, axiom,
% 1.76/2.00    (![A:$i,B:$i,C:$i]:
% 1.76/2.00     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 1.76/2.00       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.76/2.00            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.76/2.00  thf('1', plain,
% 1.76/2.00      (![X74 : $i, X76 : $i, X77 : $i]:
% 1.76/2.00         ((r1_tarski @ X76 @ (k2_tarski @ X74 @ X77))
% 1.76/2.00          | ((X76) != (k1_tarski @ X74)))),
% 1.76/2.00      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.76/2.00  thf('2', plain,
% 1.76/2.00      (![X74 : $i, X77 : $i]:
% 1.76/2.00         (r1_tarski @ (k1_tarski @ X74) @ (k2_tarski @ X74 @ X77))),
% 1.76/2.00      inference('simplify', [status(thm)], ['1'])).
% 1.76/2.00  thf(t28_zfmisc_1, conjecture,
% 1.76/2.00    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/2.00     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 1.76/2.00          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 1.76/2.00  thf(zf_stmt_1, negated_conjecture,
% 1.76/2.00    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.76/2.00        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 1.76/2.00             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 1.76/2.00    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 1.76/2.00  thf('3', plain,
% 1.76/2.00      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.76/2.00  thf(t28_xboole_1, axiom,
% 1.76/2.00    (![A:$i,B:$i]:
% 1.76/2.00     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.76/2.00  thf('4', plain,
% 1.76/2.00      (![X12 : $i, X13 : $i]:
% 1.76/2.00         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.76/2.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/2.00  thf('5', plain,
% 1.76/2.00      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 1.76/2.00         = (k2_tarski @ sk_A @ sk_B))),
% 1.76/2.00      inference('sup-', [status(thm)], ['3', '4'])).
% 1.76/2.00  thf(commutativity_k3_xboole_0, axiom,
% 1.76/2.00    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.76/2.00  thf('6', plain,
% 1.76/2.00      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.76/2.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/2.00  thf(t18_xboole_1, axiom,
% 1.76/2.00    (![A:$i,B:$i,C:$i]:
% 1.76/2.00     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 1.76/2.00  thf('7', plain,
% 1.76/2.00      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.76/2.00         ((r1_tarski @ X9 @ X10)
% 1.76/2.00          | ~ (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t18_xboole_1])).
% 1.76/2.00  thf('8', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.00         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.76/2.00      inference('sup-', [status(thm)], ['6', '7'])).
% 1.76/2.00  thf('9', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.76/2.00          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D)))),
% 1.76/2.00      inference('sup-', [status(thm)], ['5', '8'])).
% 1.76/2.00  thf('10', plain,
% 1.76/2.00      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.00      inference('sup-', [status(thm)], ['2', '9'])).
% 1.76/2.00  thf('11', plain,
% 1.76/2.00      (![X12 : $i, X13 : $i]:
% 1.76/2.00         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.76/2.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/2.00  thf('12', plain,
% 1.76/2.00      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 1.76/2.00         = (k1_tarski @ sk_A))),
% 1.76/2.00      inference('sup-', [status(thm)], ['10', '11'])).
% 1.76/2.00  thf(t100_xboole_1, axiom,
% 1.76/2.00    (![A:$i,B:$i]:
% 1.76/2.00     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.76/2.00  thf('13', plain,
% 1.76/2.00      (![X5 : $i, X6 : $i]:
% 1.76/2.00         ((k4_xboole_0 @ X5 @ X6)
% 1.76/2.00           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.76/2.00  thf('14', plain,
% 1.76/2.00      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 1.76/2.00         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['12', '13'])).
% 1.76/2.00  thf(t17_xboole_1, axiom,
% 1.76/2.00    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.76/2.00  thf('15', plain,
% 1.76/2.00      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.76/2.00      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.76/2.00  thf(t3_xboole_1, axiom,
% 1.76/2.00    (![A:$i]:
% 1.76/2.00     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.76/2.00  thf('16', plain,
% 1.76/2.00      (![X14 : $i]:
% 1.76/2.00         (((X14) = (k1_xboole_0)) | ~ (r1_tarski @ X14 @ k1_xboole_0))),
% 1.76/2.00      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.76/2.00  thf('17', plain,
% 1.76/2.00      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.76/2.00      inference('sup-', [status(thm)], ['15', '16'])).
% 1.76/2.00  thf('18', plain,
% 1.76/2.00      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.76/2.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/2.00  thf('19', plain,
% 1.76/2.00      (![X5 : $i, X6 : $i]:
% 1.76/2.00         ((k4_xboole_0 @ X5 @ X6)
% 1.76/2.00           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.76/2.00  thf('20', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]:
% 1.76/2.00         ((k4_xboole_0 @ X0 @ X1)
% 1.76/2.00           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['18', '19'])).
% 1.76/2.00  thf('21', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['17', '20'])).
% 1.76/2.00  thf(t5_boole, axiom,
% 1.76/2.00    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.76/2.00  thf('22', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.76/2.00      inference('cnf', [status(esa)], [t5_boole])).
% 1.76/2.00  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.76/2.00      inference('demod', [status(thm)], ['21', '22'])).
% 1.76/2.00  thf(t48_xboole_1, axiom,
% 1.76/2.00    (![A:$i,B:$i]:
% 1.76/2.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.76/2.00  thf('24', plain,
% 1.76/2.00      (![X15 : $i, X16 : $i]:
% 1.76/2.00         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.76/2.00           = (k3_xboole_0 @ X15 @ X16))),
% 1.76/2.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.76/2.00  thf('25', plain,
% 1.76/2.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['23', '24'])).
% 1.76/2.00  thf(idempotence_k3_xboole_0, axiom,
% 1.76/2.00    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.76/2.00  thf('26', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.76/2.00      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.76/2.00  thf('27', plain,
% 1.76/2.00      (![X5 : $i, X6 : $i]:
% 1.76/2.00         ((k4_xboole_0 @ X5 @ X6)
% 1.76/2.00           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.76/2.00  thf('28', plain,
% 1.76/2.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['26', '27'])).
% 1.76/2.00  thf('29', plain,
% 1.76/2.00      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.76/2.00      inference('sup-', [status(thm)], ['15', '16'])).
% 1.76/2.00  thf('30', plain,
% 1.76/2.00      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.76/2.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/2.00  thf('31', plain,
% 1.76/2.00      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['29', '30'])).
% 1.76/2.00  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.76/2.00      inference('demod', [status(thm)], ['25', '28', '31'])).
% 1.76/2.00  thf('33', plain,
% 1.76/2.00      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 1.76/2.00         = (k1_xboole_0))),
% 1.76/2.00      inference('demod', [status(thm)], ['14', '32'])).
% 1.76/2.00  thf(t98_xboole_1, axiom,
% 1.76/2.00    (![A:$i,B:$i]:
% 1.76/2.00     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.76/2.00  thf('34', plain,
% 1.76/2.00      (![X18 : $i, X19 : $i]:
% 1.76/2.00         ((k2_xboole_0 @ X18 @ X19)
% 1.76/2.00           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.76/2.00  thf('35', plain,
% 1.76/2.00      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_A))
% 1.76/2.00         = (k5_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ k1_xboole_0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['33', '34'])).
% 1.76/2.00  thf(commutativity_k2_xboole_0, axiom,
% 1.76/2.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.76/2.00  thf('36', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.76/2.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.76/2.00  thf('37', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.76/2.00      inference('cnf', [status(esa)], [t5_boole])).
% 1.76/2.00  thf('38', plain,
% 1.76/2.00      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 1.76/2.00         = (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.00      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.76/2.00  thf(t70_enumset1, axiom,
% 1.76/2.00    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.76/2.00  thf('39', plain,
% 1.76/2.00      (![X44 : $i, X45 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.76/2.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.76/2.00  thf(t44_enumset1, axiom,
% 1.76/2.00    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/2.00     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.76/2.00       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 1.76/2.00  thf('40', plain,
% 1.76/2.00      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X35 @ X36 @ X37 @ X38)
% 1.76/2.00           = (k2_xboole_0 @ (k1_tarski @ X35) @ (k1_enumset1 @ X36 @ X37 @ X38)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t44_enumset1])).
% 1.76/2.00  thf('41', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 1.76/2.00           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['39', '40'])).
% 1.76/2.00  thf('42', plain,
% 1.76/2.00      (((k2_enumset1 @ sk_A @ sk_C @ sk_C @ sk_D) = (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.00      inference('demod', [status(thm)], ['38', '41'])).
% 1.76/2.00  thf('43', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.76/2.00      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.76/2.00  thf('44', plain,
% 1.76/2.00      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.76/2.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/2.00  thf('45', plain,
% 1.76/2.00      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.76/2.00      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.76/2.00  thf('46', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.76/2.00      inference('sup+', [status(thm)], ['44', '45'])).
% 1.76/2.00  thf('47', plain,
% 1.76/2.00      (![X74 : $i, X76 : $i, X77 : $i]:
% 1.76/2.00         ((r1_tarski @ X76 @ (k2_tarski @ X74 @ X77))
% 1.76/2.00          | ((X76) != (k1_tarski @ X77)))),
% 1.76/2.00      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.76/2.00  thf('48', plain,
% 1.76/2.00      (![X74 : $i, X77 : $i]:
% 1.76/2.00         (r1_tarski @ (k1_tarski @ X77) @ (k2_tarski @ X74 @ X77))),
% 1.76/2.00      inference('simplify', [status(thm)], ['47'])).
% 1.76/2.00  thf('49', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.76/2.00          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D)))),
% 1.76/2.00      inference('sup-', [status(thm)], ['5', '8'])).
% 1.76/2.00  thf('50', plain,
% 1.76/2.00      ((r1_tarski @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.00      inference('sup-', [status(thm)], ['48', '49'])).
% 1.76/2.00  thf('51', plain,
% 1.76/2.00      (![X12 : $i, X13 : $i]:
% 1.76/2.00         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.76/2.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/2.00  thf('52', plain,
% 1.76/2.00      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 1.76/2.00         = (k1_tarski @ sk_B))),
% 1.76/2.00      inference('sup-', [status(thm)], ['50', '51'])).
% 1.76/2.00  thf('53', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.00         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.76/2.00      inference('sup-', [status(thm)], ['6', '7'])).
% 1.76/2.00  thf('54', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_B))
% 1.76/2.00          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D)))),
% 1.76/2.00      inference('sup-', [status(thm)], ['52', '53'])).
% 1.76/2.00  thf('55', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)) @ 
% 1.76/2.00          (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.00      inference('sup-', [status(thm)], ['46', '54'])).
% 1.76/2.00  thf('56', plain,
% 1.76/2.00      (![X12 : $i, X13 : $i]:
% 1.76/2.00         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.76/2.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/2.00  thf('57', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)) @ 
% 1.76/2.00           (k2_tarski @ sk_C @ sk_D)) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))),
% 1.76/2.00      inference('sup-', [status(thm)], ['55', '56'])).
% 1.76/2.00  thf('58', plain,
% 1.76/2.00      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.76/2.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/2.00  thf('59', plain,
% 1.76/2.00      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.76/2.00      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.76/2.00  thf('60', plain,
% 1.76/2.00      (![X12 : $i, X13 : $i]:
% 1.76/2.00         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.76/2.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.76/2.00  thf('61', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]:
% 1.76/2.00         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.76/2.00           = (k3_xboole_0 @ X0 @ X1))),
% 1.76/2.00      inference('sup-', [status(thm)], ['59', '60'])).
% 1.76/2.00  thf('62', plain,
% 1.76/2.00      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.76/2.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.76/2.00  thf('63', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]:
% 1.76/2.00         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.76/2.00           = (k3_xboole_0 @ X0 @ X1))),
% 1.76/2.00      inference('demod', [status(thm)], ['61', '62'])).
% 1.76/2.00  thf('64', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]:
% 1.76/2.00         ((k4_xboole_0 @ X0 @ X1)
% 1.76/2.00           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['18', '19'])).
% 1.76/2.00  thf('65', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]:
% 1.76/2.00         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.76/2.00           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['63', '64'])).
% 1.76/2.00  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.76/2.00      inference('demod', [status(thm)], ['25', '28', '31'])).
% 1.76/2.00  thf('67', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]:
% 1.76/2.00         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.76/2.00      inference('demod', [status(thm)], ['65', '66'])).
% 1.76/2.00  thf('68', plain,
% 1.76/2.00      (![X18 : $i, X19 : $i]:
% 1.76/2.00         ((k2_xboole_0 @ X18 @ X19)
% 1.76/2.00           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.76/2.00  thf('69', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]:
% 1.76/2.00         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.76/2.00           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['67', '68'])).
% 1.76/2.00  thf('70', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.76/2.00      inference('cnf', [status(esa)], [t5_boole])).
% 1.76/2.00  thf('71', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]:
% 1.76/2.00         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.76/2.00      inference('demod', [status(thm)], ['69', '70'])).
% 1.76/2.00  thf('72', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]:
% 1.76/2.00         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['58', '71'])).
% 1.76/2.00  thf('73', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         ((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ 
% 1.76/2.00           (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B))) = (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.00      inference('sup+', [status(thm)], ['57', '72'])).
% 1.76/2.00  thf('74', plain,
% 1.76/2.00      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_B))
% 1.76/2.00         = (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.00      inference('sup+', [status(thm)], ['43', '73'])).
% 1.76/2.00  thf('75', plain,
% 1.76/2.00      (![X44 : $i, X45 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.76/2.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.76/2.00  thf(t46_enumset1, axiom,
% 1.76/2.00    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/2.00     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.76/2.00       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 1.76/2.00  thf('76', plain,
% 1.76/2.00      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X39 @ X40 @ X41 @ X42)
% 1.76/2.00           = (k2_xboole_0 @ (k1_enumset1 @ X39 @ X40 @ X41) @ (k1_tarski @ X42)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t46_enumset1])).
% 1.76/2.00  thf('77', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 1.76/2.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['75', '76'])).
% 1.76/2.00  thf(t71_enumset1, axiom,
% 1.76/2.00    (![A:$i,B:$i,C:$i]:
% 1.76/2.00     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.76/2.00  thf('78', plain,
% 1.76/2.00      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 1.76/2.00           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 1.76/2.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.76/2.00  thf(t102_enumset1, axiom,
% 1.76/2.00    (![A:$i,B:$i,C:$i]:
% 1.76/2.00     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 1.76/2.00  thf('79', plain,
% 1.76/2.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X34 @ X33 @ X32) = (k1_enumset1 @ X32 @ X33 @ X34))),
% 1.76/2.00      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.76/2.00  thf('80', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['78', '79'])).
% 1.76/2.00  thf(t98_enumset1, axiom,
% 1.76/2.00    (![A:$i,B:$i,C:$i]:
% 1.76/2.00     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 1.76/2.00  thf('81', plain,
% 1.76/2.00      (![X71 : $i, X72 : $i, X73 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X71 @ X73 @ X72) = (k1_enumset1 @ X71 @ X72 @ X73))),
% 1.76/2.00      inference('cnf', [status(esa)], [t98_enumset1])).
% 1.76/2.00  thf('82', plain,
% 1.76/2.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X34 @ X33 @ X32) = (k1_enumset1 @ X32 @ X33 @ X34))),
% 1.76/2.00      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.76/2.00  thf('83', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['81', '82'])).
% 1.76/2.00  thf('84', plain,
% 1.76/2.00      (![X71 : $i, X72 : $i, X73 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X71 @ X73 @ X72) = (k1_enumset1 @ X71 @ X72 @ X73))),
% 1.76/2.00      inference('cnf', [status(esa)], [t98_enumset1])).
% 1.76/2.00  thf('85', plain,
% 1.76/2.00      (((k1_enumset1 @ sk_C @ sk_D @ sk_B) = (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.00      inference('demod', [status(thm)], ['74', '77', '80', '83', '84'])).
% 1.76/2.00  thf('86', plain,
% 1.76/2.00      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X35 @ X36 @ X37 @ X38)
% 1.76/2.00           = (k2_xboole_0 @ (k1_tarski @ X35) @ (k1_enumset1 @ X36 @ X37 @ X38)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t44_enumset1])).
% 1.76/2.00  thf('87', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.76/2.00      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.76/2.00  thf('88', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.76/2.00         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 1.76/2.00           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['86', '87'])).
% 1.76/2.00  thf('89', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         ((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ X0))
% 1.76/2.00           = (k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B))),
% 1.76/2.00      inference('sup+', [status(thm)], ['85', '88'])).
% 1.76/2.00  thf('90', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 1.76/2.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['75', '76'])).
% 1.76/2.00  thf('91', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.76/2.00      inference('sup+', [status(thm)], ['78', '79'])).
% 1.76/2.00  thf('92', plain,
% 1.76/2.00      (![X71 : $i, X72 : $i, X73 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X71 @ X73 @ X72) = (k1_enumset1 @ X71 @ X72 @ X73))),
% 1.76/2.00      inference('cnf', [status(esa)], [t98_enumset1])).
% 1.76/2.00  thf('93', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X0 @ sk_C @ sk_D)
% 1.76/2.00           = (k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B))),
% 1.76/2.00      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 1.76/2.00  thf('94', plain,
% 1.76/2.00      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 1.76/2.00           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 1.76/2.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.76/2.00  thf('95', plain,
% 1.76/2.00      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X35 @ X36 @ X37 @ X38)
% 1.76/2.00           = (k2_xboole_0 @ (k1_tarski @ X35) @ (k1_enumset1 @ X36 @ X37 @ X38)))),
% 1.76/2.00      inference('cnf', [status(esa)], [t44_enumset1])).
% 1.76/2.00  thf('96', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 1.76/2.00           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 1.76/2.00              (k2_enumset1 @ X2 @ X2 @ X1 @ X0)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['94', '95'])).
% 1.76/2.00  thf('97', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B)
% 1.76/2.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 1.76/2.00              (k1_enumset1 @ sk_C @ sk_C @ sk_D)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['93', '96'])).
% 1.76/2.00  thf('98', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X0 @ sk_C @ sk_D)
% 1.76/2.00           = (k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B))),
% 1.76/2.00      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 1.76/2.00  thf('99', plain,
% 1.76/2.00      (![X44 : $i, X45 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.76/2.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.76/2.00  thf('100', plain,
% 1.76/2.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.00         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 1.76/2.00           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 1.76/2.00      inference('sup+', [status(thm)], ['39', '40'])).
% 1.76/2.00  thf('101', plain,
% 1.76/2.00      (![X0 : $i]:
% 1.76/2.00         ((k1_enumset1 @ X0 @ sk_C @ sk_D)
% 1.76/2.00           = (k2_enumset1 @ X0 @ sk_C @ sk_C @ sk_D))),
% 1.76/2.00      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 1.76/2.01  thf('102', plain,
% 1.76/2.01      (((k1_enumset1 @ sk_A @ sk_C @ sk_D) = (k2_tarski @ sk_C @ sk_D))),
% 1.76/2.01      inference('demod', [status(thm)], ['42', '101'])).
% 1.76/2.01  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.76/2.01  thf(zf_stmt_3, axiom,
% 1.76/2.01    (![A:$i,B:$i,C:$i,D:$i]:
% 1.76/2.01     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.76/2.01       ( ![E:$i]:
% 1.76/2.01         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.76/2.01  thf('103', plain,
% 1.76/2.01      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.76/2.01         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 1.76/2.01          | (r2_hidden @ X25 @ X29)
% 1.76/2.01          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.76/2.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.76/2.01  thf('104', plain,
% 1.76/2.01      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.76/2.01         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 1.76/2.01          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 1.76/2.01      inference('simplify', [status(thm)], ['103'])).
% 1.76/2.01  thf('105', plain,
% 1.76/2.01      (![X0 : $i]:
% 1.76/2.01         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D))
% 1.76/2.01          | (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A))),
% 1.76/2.01      inference('sup+', [status(thm)], ['102', '104'])).
% 1.76/2.01  thf('106', plain,
% 1.76/2.01      (![X44 : $i, X45 : $i]:
% 1.76/2.01         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.76/2.01      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.76/2.01  thf('107', plain,
% 1.76/2.01      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.76/2.01         (~ (r2_hidden @ X30 @ X29)
% 1.76/2.01          | ~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 1.76/2.01          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.76/2.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.76/2.01  thf('108', plain,
% 1.76/2.01      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 1.76/2.01         (~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 1.76/2.01          | ~ (r2_hidden @ X30 @ (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.76/2.01      inference('simplify', [status(thm)], ['107'])).
% 1.76/2.01  thf('109', plain,
% 1.76/2.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.76/2.01         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.76/2.01          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.76/2.01      inference('sup-', [status(thm)], ['106', '108'])).
% 1.76/2.01  thf('110', plain,
% 1.76/2.01      (![X0 : $i]:
% 1.76/2.01         ((zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A)
% 1.76/2.01          | ~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_C))),
% 1.76/2.01      inference('sup-', [status(thm)], ['105', '109'])).
% 1.76/2.01  thf('111', plain,
% 1.76/2.01      (![X0 : $i]:
% 1.76/2.01         (((X0) = (sk_C))
% 1.76/2.01          | ((X0) = (sk_C))
% 1.76/2.01          | ((X0) = (sk_D))
% 1.76/2.01          | (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A))),
% 1.76/2.01      inference('sup-', [status(thm)], ['0', '110'])).
% 1.76/2.01  thf('112', plain,
% 1.76/2.01      (![X0 : $i]:
% 1.76/2.01         ((zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_A)
% 1.76/2.01          | ((X0) = (sk_D))
% 1.76/2.01          | ((X0) = (sk_C)))),
% 1.76/2.01      inference('simplify', [status(thm)], ['111'])).
% 1.76/2.01  thf('113', plain,
% 1.76/2.01      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.76/2.01         (((X21) != (X20)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 1.76/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.76/2.01  thf('114', plain,
% 1.76/2.01      (![X20 : $i, X22 : $i, X23 : $i]:
% 1.76/2.01         ~ (zip_tseitin_0 @ X20 @ X22 @ X23 @ X20)),
% 1.76/2.01      inference('simplify', [status(thm)], ['113'])).
% 1.76/2.01  thf('115', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_D)))),
% 1.76/2.01      inference('sup-', [status(thm)], ['112', '114'])).
% 1.76/2.01  thf('116', plain, (((sk_A) != (sk_D))),
% 1.76/2.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.76/2.01  thf('117', plain, (((sk_A) != (sk_C))),
% 1.76/2.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.76/2.01  thf('118', plain, ($false),
% 1.76/2.01      inference('simplify_reflect-', [status(thm)], ['115', '116', '117'])).
% 1.76/2.01  
% 1.76/2.01  % SZS output end Refutation
% 1.76/2.01  
% 1.76/2.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
