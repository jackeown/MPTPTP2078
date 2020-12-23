%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tdUTCe0ZTw

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:32 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 278 expanded)
%              Number of leaves         :   31 ( 108 expanded)
%              Depth                    :   19
%              Number of atoms          : 1076 (2382 expanded)
%              Number of equality atoms :  118 ( 274 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( X18 = X19 )
      | ( X18 = X20 )
      | ( X18 = X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8','9','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','22'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X4 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X4 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X4 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['1','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8','9','21'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','20'])).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('56',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('57',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','60'])).

thf('62',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('64',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('66',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('68',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['62','63','64','65','66','67'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('69',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('71',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('74',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('75',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['68','77'])).

thf('79',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
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

thf('80',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X22 @ X26 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('81',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','81'])).

thf('83',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X19 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ~ ( zip_tseitin_0 @ X19 @ X19 @ X20 @ X17 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['78','85'])).

thf('87',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('88',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('89',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X23 @ X24 @ X25 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('90',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X23 @ X24 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','93'])).

thf('95',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tdUTCe0ZTw
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 1.83/2.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.83/2.11  % Solved by: fo/fo7.sh
% 1.83/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.83/2.11  % done 2128 iterations in 1.661s
% 1.83/2.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.83/2.11  % SZS output start Refutation
% 1.83/2.11  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.83/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.83/2.11  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.83/2.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.83/2.11  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.83/2.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.83/2.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.83/2.11  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.83/2.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.83/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.83/2.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.83/2.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.83/2.11  thf(d1_enumset1, axiom,
% 1.83/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.83/2.11     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.83/2.11       ( ![E:$i]:
% 1.83/2.11         ( ( r2_hidden @ E @ D ) <=>
% 1.83/2.11           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.83/2.11  thf(zf_stmt_0, axiom,
% 1.83/2.11    (![E:$i,C:$i,B:$i,A:$i]:
% 1.83/2.11     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.83/2.11       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.83/2.11  thf('0', plain,
% 1.83/2.11      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.83/2.11         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 1.83/2.11          | ((X18) = (X19))
% 1.83/2.11          | ((X18) = (X20))
% 1.83/2.11          | ((X18) = (X21)))),
% 1.83/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.83/2.11  thf(t18_zfmisc_1, conjecture,
% 1.83/2.11    (![A:$i,B:$i]:
% 1.83/2.11     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.83/2.11         ( k1_tarski @ A ) ) =>
% 1.83/2.11       ( ( A ) = ( B ) ) ))).
% 1.83/2.11  thf(zf_stmt_1, negated_conjecture,
% 1.83/2.11    (~( ![A:$i,B:$i]:
% 1.83/2.11        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.83/2.11            ( k1_tarski @ A ) ) =>
% 1.83/2.11          ( ( A ) = ( B ) ) ) )),
% 1.83/2.11    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 1.83/2.11  thf('1', plain,
% 1.83/2.11      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.83/2.11         = (k1_tarski @ sk_A))),
% 1.83/2.11      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.83/2.11  thf(t21_xboole_1, axiom,
% 1.83/2.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.83/2.11  thf('2', plain,
% 1.83/2.11      (![X7 : $i, X8 : $i]:
% 1.83/2.11         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 1.83/2.11      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.83/2.11  thf(t94_xboole_1, axiom,
% 1.83/2.11    (![A:$i,B:$i]:
% 1.83/2.11     ( ( k2_xboole_0 @ A @ B ) =
% 1.83/2.11       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.83/2.11  thf('3', plain,
% 1.83/2.11      (![X13 : $i, X14 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ X13 @ X14)
% 1.83/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 1.83/2.11              (k3_xboole_0 @ X13 @ X14)))),
% 1.83/2.11      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.83/2.11  thf(commutativity_k2_xboole_0, axiom,
% 1.83/2.11    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.83/2.11  thf('4', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.83/2.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.83/2.11  thf(t95_xboole_1, axiom,
% 1.83/2.11    (![A:$i,B:$i]:
% 1.83/2.11     ( ( k3_xboole_0 @ A @ B ) =
% 1.83/2.11       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.83/2.11  thf('5', plain,
% 1.83/2.11      (![X15 : $i, X16 : $i]:
% 1.83/2.11         ((k3_xboole_0 @ X15 @ X16)
% 1.83/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ 
% 1.83/2.11              (k2_xboole_0 @ X15 @ X16)))),
% 1.83/2.11      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.83/2.11  thf('6', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]:
% 1.83/2.11         ((k3_xboole_0 @ X0 @ X1)
% 1.83/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.83/2.11      inference('sup+', [status(thm)], ['4', '5'])).
% 1.83/2.11  thf('7', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]:
% 1.83/2.11         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.83/2.11           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.83/2.11              (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 1.83/2.11      inference('sup+', [status(thm)], ['3', '6'])).
% 1.83/2.11  thf('8', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.83/2.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.83/2.11  thf(t93_xboole_1, axiom,
% 1.83/2.11    (![A:$i,B:$i]:
% 1.83/2.11     ( ( k2_xboole_0 @ A @ B ) =
% 1.83/2.11       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.83/2.11  thf('9', plain,
% 1.83/2.11      (![X11 : $i, X12 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ X11 @ X12)
% 1.83/2.11           = (k2_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 1.83/2.11              (k3_xboole_0 @ X11 @ X12)))),
% 1.83/2.11      inference('cnf', [status(esa)], [t93_xboole_1])).
% 1.83/2.11  thf(t5_boole, axiom,
% 1.83/2.11    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.83/2.11  thf('10', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.83/2.11      inference('cnf', [status(esa)], [t5_boole])).
% 1.83/2.11  thf('11', plain,
% 1.83/2.11      (![X15 : $i, X16 : $i]:
% 1.83/2.11         ((k3_xboole_0 @ X15 @ X16)
% 1.83/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ 
% 1.83/2.11              (k2_xboole_0 @ X15 @ X16)))),
% 1.83/2.11      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.83/2.11  thf('12', plain,
% 1.83/2.11      (![X0 : $i]:
% 1.83/2.11         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 1.83/2.11           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.83/2.11      inference('sup+', [status(thm)], ['10', '11'])).
% 1.83/2.11  thf(t2_boole, axiom,
% 1.83/2.11    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.83/2.11  thf('13', plain,
% 1.83/2.11      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 1.83/2.11      inference('cnf', [status(esa)], [t2_boole])).
% 1.83/2.11  thf('14', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.83/2.11      inference('cnf', [status(esa)], [t5_boole])).
% 1.83/2.11  thf('15', plain,
% 1.83/2.11      (![X13 : $i, X14 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ X13 @ X14)
% 1.83/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 1.83/2.11              (k3_xboole_0 @ X13 @ X14)))),
% 1.83/2.11      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.83/2.11  thf('16', plain,
% 1.83/2.11      (![X0 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 1.83/2.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.83/2.11      inference('sup+', [status(thm)], ['14', '15'])).
% 1.83/2.11  thf('17', plain,
% 1.83/2.11      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 1.83/2.11      inference('cnf', [status(esa)], [t2_boole])).
% 1.83/2.11  thf('18', plain,
% 1.83/2.11      (![X0 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.83/2.11      inference('demod', [status(thm)], ['16', '17'])).
% 1.83/2.11  thf('19', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.83/2.11      inference('cnf', [status(esa)], [t5_boole])).
% 1.83/2.11  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.83/2.11      inference('demod', [status(thm)], ['18', '19'])).
% 1.83/2.11  thf('21', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.83/2.11      inference('demod', [status(thm)], ['12', '13', '20'])).
% 1.83/2.11  thf('22', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]:
% 1.83/2.11         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.83/2.11           = (k1_xboole_0))),
% 1.83/2.11      inference('demod', [status(thm)], ['7', '8', '9', '21'])).
% 1.83/2.11  thf('23', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]:
% 1.83/2.11         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X0)
% 1.83/2.11           = (k1_xboole_0))),
% 1.83/2.11      inference('sup+', [status(thm)], ['2', '22'])).
% 1.83/2.11  thf(t112_xboole_1, axiom,
% 1.83/2.11    (![A:$i,B:$i,C:$i]:
% 1.83/2.11     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.83/2.11       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.83/2.11  thf('24', plain,
% 1.83/2.11      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.83/2.11         ((k5_xboole_0 @ (k3_xboole_0 @ X4 @ X6) @ (k3_xboole_0 @ X5 @ X6))
% 1.83/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6))),
% 1.83/2.11      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.83/2.11  thf('25', plain,
% 1.83/2.11      (![X11 : $i, X12 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ X11 @ X12)
% 1.83/2.11           = (k2_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 1.83/2.11              (k3_xboole_0 @ X11 @ X12)))),
% 1.83/2.11      inference('cnf', [status(esa)], [t93_xboole_1])).
% 1.83/2.11  thf('26', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.83/2.11           = (k2_xboole_0 @ (k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0) @ 
% 1.83/2.11              (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 1.83/2.11      inference('sup+', [status(thm)], ['24', '25'])).
% 1.83/2.11  thf('27', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ 
% 1.83/2.11           (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 1.83/2.11           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.83/2.11              (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ 
% 1.83/2.11               (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))))),
% 1.83/2.11      inference('sup+', [status(thm)], ['23', '26'])).
% 1.83/2.11  thf(idempotence_k3_xboole_0, axiom,
% 1.83/2.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.83/2.11  thf('28', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.83/2.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.83/2.11  thf('29', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.83/2.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.83/2.11  thf('30', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.83/2.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.83/2.11  thf('31', plain,
% 1.83/2.11      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.83/2.11         ((k5_xboole_0 @ (k3_xboole_0 @ X4 @ X6) @ (k3_xboole_0 @ X5 @ X6))
% 1.83/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6))),
% 1.83/2.11      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.83/2.11  thf('32', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]:
% 1.83/2.11         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.83/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 1.83/2.11      inference('sup+', [status(thm)], ['30', '31'])).
% 1.83/2.11  thf('33', plain,
% 1.83/2.11      (![X13 : $i, X14 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ X13 @ X14)
% 1.83/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 1.83/2.11              (k3_xboole_0 @ X13 @ X14)))),
% 1.83/2.11      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.83/2.11  thf('34', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]:
% 1.83/2.11         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.83/2.11           = (k5_xboole_0 @ (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0) @ 
% 1.83/2.11              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)))),
% 1.83/2.11      inference('sup+', [status(thm)], ['32', '33'])).
% 1.83/2.11  thf('35', plain,
% 1.83/2.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.83/2.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.83/2.11  thf('36', plain,
% 1.83/2.11      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.83/2.11         ((k5_xboole_0 @ (k3_xboole_0 @ X4 @ X6) @ (k3_xboole_0 @ X5 @ X6))
% 1.83/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6))),
% 1.83/2.11      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.94/2.11  thf('37', plain,
% 1.94/2.11      (![X13 : $i, X14 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X13 @ X14)
% 1.94/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 1.94/2.11              (k3_xboole_0 @ X13 @ X14)))),
% 1.94/2.11      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.94/2.11  thf('38', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.94/2.11           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.94/2.11      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 1.94/2.11  thf('39', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.94/2.11           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.94/2.11      inference('sup+', [status(thm)], ['29', '38'])).
% 1.94/2.11  thf('40', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.94/2.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.94/2.11  thf('41', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.94/2.11           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.94/2.11      inference('sup+', [status(thm)], ['29', '38'])).
% 1.94/2.11  thf('42', plain,
% 1.94/2.11      (![X7 : $i, X8 : $i]:
% 1.94/2.11         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 1.94/2.11      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.94/2.11  thf('43', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.94/2.11           = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.94/2.11      inference('demod', [status(thm)], ['27', '28', '39', '40', '41', '42'])).
% 1.94/2.11  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.94/2.11      inference('demod', [status(thm)], ['18', '19'])).
% 1.94/2.11  thf('45', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.11  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.94/2.11      inference('sup+', [status(thm)], ['44', '45'])).
% 1.94/2.11  thf('47', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.94/2.11           = (X0))),
% 1.94/2.11      inference('demod', [status(thm)], ['43', '46'])).
% 1.94/2.11  thf('48', plain,
% 1.94/2.11      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ 
% 1.94/2.11         (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 1.94/2.11         = (k1_tarski @ sk_B))),
% 1.94/2.11      inference('sup+', [status(thm)], ['1', '47'])).
% 1.94/2.11  thf('49', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.94/2.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.94/2.11  thf('50', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.94/2.11           = (k1_xboole_0))),
% 1.94/2.11      inference('demod', [status(thm)], ['7', '8', '9', '21'])).
% 1.94/2.11  thf('51', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.94/2.11           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 1.94/2.11      inference('sup+', [status(thm)], ['30', '31'])).
% 1.94/2.11  thf('52', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 1.94/2.11           = (k3_xboole_0 @ 
% 1.94/2.11              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.94/2.11              (k3_xboole_0 @ X1 @ X0)))),
% 1.94/2.11      inference('sup+', [status(thm)], ['50', '51'])).
% 1.94/2.11  thf('53', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.94/2.11      inference('demod', [status(thm)], ['12', '13', '20'])).
% 1.94/2.11  thf('54', plain,
% 1.94/2.11      (![X13 : $i, X14 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X13 @ X14)
% 1.94/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 1.94/2.11              (k3_xboole_0 @ X13 @ X14)))),
% 1.94/2.11      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.94/2.11  thf('55', plain,
% 1.94/2.11      (![X0 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X0 @ X0)
% 1.94/2.11           = (k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 1.94/2.11      inference('sup+', [status(thm)], ['53', '54'])).
% 1.94/2.11  thf(idempotence_k2_xboole_0, axiom,
% 1.94/2.11    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.94/2.11  thf('56', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.94/2.11      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.94/2.11  thf('57', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.94/2.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.94/2.11  thf('58', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.94/2.11      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.94/2.11  thf('59', plain,
% 1.94/2.11      (![X13 : $i, X14 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X13 @ X14)
% 1.94/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 1.94/2.11              (k3_xboole_0 @ X13 @ X14)))),
% 1.94/2.11      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.94/2.11  thf('60', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k3_xboole_0 @ X1 @ X0)
% 1.94/2.11           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.94/2.11      inference('demod', [status(thm)], ['52', '58', '59'])).
% 1.94/2.11  thf('61', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k3_xboole_0 @ X0 @ X1)
% 1.94/2.11           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.94/2.11      inference('sup+', [status(thm)], ['49', '60'])).
% 1.94/2.11  thf('62', plain,
% 1.94/2.11      (((k3_xboole_0 @ 
% 1.94/2.11         (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 1.94/2.11         (k1_tarski @ sk_B))
% 1.94/2.11         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ 
% 1.94/2.11            (k3_xboole_0 @ 
% 1.94/2.11             (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 1.94/2.11             (k1_tarski @ sk_B))))),
% 1.94/2.11      inference('sup+', [status(thm)], ['48', '61'])).
% 1.94/2.11  thf('63', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.94/2.11           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.94/2.11      inference('sup+', [status(thm)], ['29', '38'])).
% 1.94/2.11  thf('64', plain,
% 1.94/2.11      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.94/2.11         = (k1_tarski @ sk_A))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.94/2.11  thf('65', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.94/2.11           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.94/2.11      inference('sup+', [status(thm)], ['29', '38'])).
% 1.94/2.11  thf('66', plain,
% 1.94/2.11      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.94/2.11         = (k1_tarski @ sk_A))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.94/2.11  thf('67', plain,
% 1.94/2.11      (![X7 : $i, X8 : $i]:
% 1.94/2.11         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 1.94/2.11      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.94/2.11  thf('68', plain,
% 1.94/2.11      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 1.94/2.11         = (k1_tarski @ sk_B))),
% 1.94/2.11      inference('demod', [status(thm)], ['62', '63', '64', '65', '66', '67'])).
% 1.94/2.11  thf(t69_enumset1, axiom,
% 1.94/2.11    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.94/2.11  thf('69', plain,
% 1.94/2.11      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 1.94/2.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.94/2.11  thf(t70_enumset1, axiom,
% 1.94/2.11    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.94/2.11  thf('70', plain,
% 1.94/2.11      (![X34 : $i, X35 : $i]:
% 1.94/2.11         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.94/2.11      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.94/2.11  thf(t46_enumset1, axiom,
% 1.94/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.11     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.94/2.11       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 1.94/2.11  thf('71', plain,
% 1.94/2.11      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.94/2.11         ((k2_enumset1 @ X29 @ X30 @ X31 @ X32)
% 1.94/2.11           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ (k1_tarski @ X32)))),
% 1.94/2.11      inference('cnf', [status(esa)], [t46_enumset1])).
% 1.94/2.11  thf('72', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.11         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 1.94/2.11           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.94/2.11      inference('sup+', [status(thm)], ['70', '71'])).
% 1.94/2.11  thf('73', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 1.94/2.11           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.94/2.11      inference('sup+', [status(thm)], ['69', '72'])).
% 1.94/2.11  thf(t71_enumset1, axiom,
% 1.94/2.11    (![A:$i,B:$i,C:$i]:
% 1.94/2.11     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.94/2.11  thf('74', plain,
% 1.94/2.11      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.94/2.11         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 1.94/2.11           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 1.94/2.11      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.94/2.11  thf('75', plain,
% 1.94/2.11      (![X34 : $i, X35 : $i]:
% 1.94/2.11         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.94/2.11      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.94/2.11  thf('76', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.94/2.11      inference('sup+', [status(thm)], ['74', '75'])).
% 1.94/2.11  thf('77', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         ((k2_tarski @ X0 @ X1)
% 1.94/2.11           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.94/2.11      inference('demod', [status(thm)], ['73', '76'])).
% 1.94/2.11  thf('78', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 1.94/2.11      inference('demod', [status(thm)], ['68', '77'])).
% 1.94/2.11  thf('79', plain,
% 1.94/2.11      (![X34 : $i, X35 : $i]:
% 1.94/2.11         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.94/2.11      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.94/2.11  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.94/2.11  thf(zf_stmt_3, axiom,
% 1.94/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.11     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.94/2.11       ( ![E:$i]:
% 1.94/2.11         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.94/2.11  thf('80', plain,
% 1.94/2.11      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.94/2.11         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 1.94/2.11          | (r2_hidden @ X22 @ X26)
% 1.94/2.11          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.94/2.11  thf('81', plain,
% 1.94/2.11      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.94/2.11         ((r2_hidden @ X22 @ (k1_enumset1 @ X25 @ X24 @ X23))
% 1.94/2.11          | (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 1.94/2.11      inference('simplify', [status(thm)], ['80'])).
% 1.94/2.11  thf('82', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.11         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.94/2.11          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.94/2.11      inference('sup+', [status(thm)], ['79', '81'])).
% 1.94/2.11  thf('83', plain,
% 1.94/2.11      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.94/2.11         (((X18) != (X19)) | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X17))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.11  thf('84', plain,
% 1.94/2.11      (![X17 : $i, X19 : $i, X20 : $i]:
% 1.94/2.11         ~ (zip_tseitin_0 @ X19 @ X19 @ X20 @ X17)),
% 1.94/2.11      inference('simplify', [status(thm)], ['83'])).
% 1.94/2.11  thf('85', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 1.94/2.11      inference('sup-', [status(thm)], ['82', '84'])).
% 1.94/2.11  thf('86', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 1.94/2.11      inference('sup+', [status(thm)], ['78', '85'])).
% 1.94/2.11  thf('87', plain,
% 1.94/2.11      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 1.94/2.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.94/2.11  thf('88', plain,
% 1.94/2.11      (![X34 : $i, X35 : $i]:
% 1.94/2.11         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.94/2.11      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.94/2.11  thf('89', plain,
% 1.94/2.11      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.94/2.11         (~ (r2_hidden @ X27 @ X26)
% 1.94/2.11          | ~ (zip_tseitin_0 @ X27 @ X23 @ X24 @ X25)
% 1.94/2.11          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.94/2.11  thf('90', plain,
% 1.94/2.11      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 1.94/2.11         (~ (zip_tseitin_0 @ X27 @ X23 @ X24 @ X25)
% 1.94/2.11          | ~ (r2_hidden @ X27 @ (k1_enumset1 @ X25 @ X24 @ X23)))),
% 1.94/2.11      inference('simplify', [status(thm)], ['89'])).
% 1.94/2.11  thf('91', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.11         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.94/2.11          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.94/2.11      inference('sup-', [status(thm)], ['88', '90'])).
% 1.94/2.11  thf('92', plain,
% 1.94/2.11      (![X0 : $i, X1 : $i]:
% 1.94/2.11         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.94/2.11          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.94/2.11      inference('sup-', [status(thm)], ['87', '91'])).
% 1.94/2.11  thf('93', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 1.94/2.11      inference('sup-', [status(thm)], ['86', '92'])).
% 1.94/2.11  thf('94', plain,
% 1.94/2.11      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 1.94/2.11      inference('sup-', [status(thm)], ['0', '93'])).
% 1.94/2.11  thf('95', plain, (((sk_A) = (sk_B))),
% 1.94/2.11      inference('simplify', [status(thm)], ['94'])).
% 1.94/2.11  thf('96', plain, (((sk_A) != (sk_B))),
% 1.94/2.11      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.94/2.11  thf('97', plain, ($false),
% 1.94/2.11      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 1.94/2.11  
% 1.94/2.11  % SZS output end Refutation
% 1.94/2.11  
% 1.94/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
