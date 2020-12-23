%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HkdRJQNdtU

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:11 EST 2020

% Result     : Theorem 9.91s
% Output     : Refutation 9.91s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 288 expanded)
%              Number of leaves         :   39 ( 108 expanded)
%              Depth                    :   20
%              Number of atoms          : 1020 (2093 expanded)
%              Number of equality atoms :  115 ( 253 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('28',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('41',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','51','52'])).

thf('54',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['41','57'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('59',plain,(
    ! [X48: $i] :
      ( ( k2_tarski @ X48 @ X48 )
      = ( k1_tarski @ X48 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('60',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( k2_enumset1 @ X51 @ X51 @ X52 @ X53 )
      = ( k1_enumset1 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('61',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_enumset1 @ X49 @ X49 @ X50 )
      = ( k2_tarski @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('63',plain,(
    ! [X63: $i,X64: $i,X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 )
      = ( k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('64',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('67',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k5_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('70',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_enumset1 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['62','71'])).

thf('73',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_enumset1 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['58','77'])).

thf('79',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_enumset1 @ X49 @ X49 @ X50 )
      = ( k2_tarski @ X49 @ X50 ) ) ),
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

thf('80',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('81',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','81'])).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['78','85'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('87',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('88',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HkdRJQNdtU
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.91/10.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.91/10.10  % Solved by: fo/fo7.sh
% 9.91/10.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.91/10.10  % done 7498 iterations in 9.638s
% 9.91/10.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.91/10.10  % SZS output start Refutation
% 9.91/10.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.91/10.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.91/10.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 9.91/10.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 9.91/10.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.91/10.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 9.91/10.10  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 9.91/10.10  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 9.91/10.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.91/10.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 9.91/10.10  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 9.91/10.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.91/10.10  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 9.91/10.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.91/10.10  thf(sk_A_type, type, sk_A: $i).
% 9.91/10.10  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 9.91/10.10  thf(sk_B_type, type, sk_B: $i).
% 9.91/10.10  thf(t13_zfmisc_1, conjecture,
% 9.91/10.10    (![A:$i,B:$i]:
% 9.91/10.10     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 9.91/10.10         ( k1_tarski @ A ) ) =>
% 9.91/10.10       ( ( A ) = ( B ) ) ))).
% 9.91/10.10  thf(zf_stmt_0, negated_conjecture,
% 9.91/10.10    (~( ![A:$i,B:$i]:
% 9.91/10.10        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 9.91/10.10            ( k1_tarski @ A ) ) =>
% 9.91/10.10          ( ( A ) = ( B ) ) ) )),
% 9.91/10.10    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 9.91/10.10  thf('0', plain,
% 9.91/10.10      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 9.91/10.10         = (k1_tarski @ sk_A))),
% 9.91/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.91/10.10  thf(t98_xboole_1, axiom,
% 9.91/10.10    (![A:$i,B:$i]:
% 9.91/10.10     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 9.91/10.10  thf('1', plain,
% 9.91/10.10      (![X14 : $i, X15 : $i]:
% 9.91/10.10         ((k2_xboole_0 @ X14 @ X15)
% 9.91/10.10           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 9.91/10.10      inference('cnf', [status(esa)], [t98_xboole_1])).
% 9.91/10.10  thf(idempotence_k3_xboole_0, axiom,
% 9.91/10.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 9.91/10.10  thf('2', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 9.91/10.10      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 9.91/10.10  thf(t100_xboole_1, axiom,
% 9.91/10.10    (![A:$i,B:$i]:
% 9.91/10.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.91/10.10  thf('3', plain,
% 9.91/10.10      (![X3 : $i, X4 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X3 @ X4)
% 9.91/10.10           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 9.91/10.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.91/10.10  thf('4', plain,
% 9.91/10.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['2', '3'])).
% 9.91/10.10  thf(t91_xboole_1, axiom,
% 9.91/10.10    (![A:$i,B:$i,C:$i]:
% 9.91/10.10     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 9.91/10.10       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 9.91/10.10  thf('5', plain,
% 9.91/10.10      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.91/10.10         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 9.91/10.10           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 9.91/10.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 9.91/10.10  thf('6', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 9.91/10.10           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['4', '5'])).
% 9.91/10.10  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.91/10.10  thf('7', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 9.91/10.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.91/10.10  thf(t28_xboole_1, axiom,
% 9.91/10.10    (![A:$i,B:$i]:
% 9.91/10.10     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.91/10.10  thf('8', plain,
% 9.91/10.10      (![X5 : $i, X6 : $i]:
% 9.91/10.10         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 9.91/10.10      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.91/10.10  thf('9', plain,
% 9.91/10.10      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 9.91/10.10      inference('sup-', [status(thm)], ['7', '8'])).
% 9.91/10.10  thf(commutativity_k3_xboole_0, axiom,
% 9.91/10.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 9.91/10.10  thf('10', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.91/10.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.91/10.10  thf('11', plain,
% 9.91/10.10      (![X3 : $i, X4 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X3 @ X4)
% 9.91/10.10           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 9.91/10.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.91/10.10  thf('12', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X0 @ X1)
% 9.91/10.10           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['10', '11'])).
% 9.91/10.10  thf('13', plain,
% 9.91/10.10      (![X0 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['9', '12'])).
% 9.91/10.10  thf(t5_boole, axiom,
% 9.91/10.10    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 9.91/10.10  thf('14', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.91/10.10      inference('cnf', [status(esa)], [t5_boole])).
% 9.91/10.10  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['13', '14'])).
% 9.91/10.10  thf(t48_xboole_1, axiom,
% 9.91/10.10    (![A:$i,B:$i]:
% 9.91/10.10     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.91/10.10  thf('16', plain,
% 9.91/10.10      (![X8 : $i, X9 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 9.91/10.10           = (k3_xboole_0 @ X8 @ X9))),
% 9.91/10.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.91/10.10  thf('17', plain,
% 9.91/10.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['15', '16'])).
% 9.91/10.10  thf('18', plain,
% 9.91/10.10      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 9.91/10.10      inference('sup-', [status(thm)], ['7', '8'])).
% 9.91/10.10  thf('19', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.91/10.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.91/10.10  thf('20', plain,
% 9.91/10.10      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['18', '19'])).
% 9.91/10.10  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.91/10.10      inference('demod', [status(thm)], ['17', '20'])).
% 9.91/10.10  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.91/10.10      inference('demod', [status(thm)], ['17', '20'])).
% 9.91/10.10  thf('23', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['21', '22'])).
% 9.91/10.10  thf('24', plain,
% 9.91/10.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['2', '3'])).
% 9.91/10.10  thf('25', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 9.91/10.10           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['4', '5'])).
% 9.91/10.10  thf('26', plain,
% 9.91/10.10      (![X0 : $i]:
% 9.91/10.10         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 9.91/10.10           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['24', '25'])).
% 9.91/10.10  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.91/10.10      inference('demod', [status(thm)], ['17', '20'])).
% 9.91/10.10  thf('28', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.91/10.10      inference('cnf', [status(esa)], [t5_boole])).
% 9.91/10.10  thf('29', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 9.91/10.10      inference('sup+', [status(thm)], ['27', '28'])).
% 9.91/10.10  thf('30', plain,
% 9.91/10.10      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 9.91/10.10      inference('demod', [status(thm)], ['26', '29'])).
% 9.91/10.10  thf('31', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 9.91/10.10      inference('sup+', [status(thm)], ['23', '30'])).
% 9.91/10.10  thf('32', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 9.91/10.10      inference('demod', [status(thm)], ['6', '31'])).
% 9.91/10.10  thf('33', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X0 @ X1)
% 9.91/10.10           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['1', '32'])).
% 9.91/10.10  thf('34', plain,
% 9.91/10.10      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 9.91/10.10         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['0', '33'])).
% 9.91/10.10  thf('35', plain,
% 9.91/10.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['2', '3'])).
% 9.91/10.10  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.91/10.10      inference('demod', [status(thm)], ['17', '20'])).
% 9.91/10.10  thf('37', plain,
% 9.91/10.10      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 9.91/10.10      inference('demod', [status(thm)], ['34', '35', '36'])).
% 9.91/10.10  thf('38', plain,
% 9.91/10.10      (![X8 : $i, X9 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 9.91/10.10           = (k3_xboole_0 @ X8 @ X9))),
% 9.91/10.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.91/10.10  thf('39', plain,
% 9.91/10.10      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 9.91/10.10         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['37', '38'])).
% 9.91/10.10  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['13', '14'])).
% 9.91/10.10  thf('41', plain,
% 9.91/10.10      (((k1_tarski @ sk_B)
% 9.91/10.10         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 9.91/10.10      inference('demod', [status(thm)], ['39', '40'])).
% 9.91/10.10  thf('42', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.91/10.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.91/10.10  thf('43', plain,
% 9.91/10.10      (![X8 : $i, X9 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 9.91/10.10           = (k3_xboole_0 @ X8 @ X9))),
% 9.91/10.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.91/10.10  thf('44', plain,
% 9.91/10.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['2', '3'])).
% 9.91/10.10  thf('45', plain,
% 9.91/10.10      (![X3 : $i, X4 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X3 @ X4)
% 9.91/10.10           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 9.91/10.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.91/10.10  thf('46', plain,
% 9.91/10.10      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.91/10.10         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 9.91/10.10           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 9.91/10.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 9.91/10.10  thf('47', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.91/10.10         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 9.91/10.10           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['45', '46'])).
% 9.91/10.10  thf('48', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 9.91/10.10           = (k5_xboole_0 @ X1 @ 
% 9.91/10.10              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 9.91/10.10      inference('sup+', [status(thm)], ['44', '47'])).
% 9.91/10.10  thf('49', plain,
% 9.91/10.10      (![X8 : $i, X9 : $i]:
% 9.91/10.10         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 9.91/10.10           = (k3_xboole_0 @ X8 @ X9))),
% 9.91/10.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.91/10.10  thf('50', plain,
% 9.91/10.10      (![X14 : $i, X15 : $i]:
% 9.91/10.10         ((k2_xboole_0 @ X14 @ X15)
% 9.91/10.10           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 9.91/10.10      inference('cnf', [status(esa)], [t98_xboole_1])).
% 9.91/10.10  thf('51', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 9.91/10.10           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['49', '50'])).
% 9.91/10.10  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.91/10.10      inference('demod', [status(thm)], ['17', '20'])).
% 9.91/10.10  thf('53', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 9.91/10.10           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 9.91/10.10      inference('demod', [status(thm)], ['48', '51', '52'])).
% 9.91/10.10  thf('54', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.91/10.10      inference('cnf', [status(esa)], [t5_boole])).
% 9.91/10.10  thf('55', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 9.91/10.10      inference('demod', [status(thm)], ['53', '54'])).
% 9.91/10.10  thf('56', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 9.91/10.10      inference('sup+', [status(thm)], ['43', '55'])).
% 9.91/10.10  thf('57', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['42', '56'])).
% 9.91/10.10  thf('58', plain,
% 9.91/10.10      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 9.91/10.10         = (k1_tarski @ sk_A))),
% 9.91/10.10      inference('sup+', [status(thm)], ['41', '57'])).
% 9.91/10.10  thf(t69_enumset1, axiom,
% 9.91/10.10    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 9.91/10.10  thf('59', plain,
% 9.91/10.10      (![X48 : $i]: ((k2_tarski @ X48 @ X48) = (k1_tarski @ X48))),
% 9.91/10.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 9.91/10.10  thf(t71_enumset1, axiom,
% 9.91/10.10    (![A:$i,B:$i,C:$i]:
% 9.91/10.10     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 9.91/10.10  thf('60', plain,
% 9.91/10.10      (![X51 : $i, X52 : $i, X53 : $i]:
% 9.91/10.10         ((k2_enumset1 @ X51 @ X51 @ X52 @ X53)
% 9.91/10.10           = (k1_enumset1 @ X51 @ X52 @ X53))),
% 9.91/10.10      inference('cnf', [status(esa)], [t71_enumset1])).
% 9.91/10.10  thf(t70_enumset1, axiom,
% 9.91/10.10    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 9.91/10.10  thf('61', plain,
% 9.91/10.10      (![X49 : $i, X50 : $i]:
% 9.91/10.10         ((k1_enumset1 @ X49 @ X49 @ X50) = (k2_tarski @ X49 @ X50))),
% 9.91/10.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 9.91/10.10  thf('62', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['60', '61'])).
% 9.91/10.10  thf(t74_enumset1, axiom,
% 9.91/10.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.91/10.10     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 9.91/10.10       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 9.91/10.10  thf('63', plain,
% 9.91/10.10      (![X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 9.91/10.10         ((k5_enumset1 @ X63 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68)
% 9.91/10.10           = (k4_enumset1 @ X63 @ X64 @ X65 @ X66 @ X67 @ X68))),
% 9.91/10.10      inference('cnf', [status(esa)], [t74_enumset1])).
% 9.91/10.10  thf(t73_enumset1, axiom,
% 9.91/10.10    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 9.91/10.10     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 9.91/10.10       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 9.91/10.10  thf('64', plain,
% 9.91/10.10      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 9.91/10.10         ((k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62)
% 9.91/10.10           = (k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 9.91/10.10      inference('cnf', [status(esa)], [t73_enumset1])).
% 9.91/10.10  thf('65', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 9.91/10.10         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 9.91/10.10           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['63', '64'])).
% 9.91/10.10  thf('66', plain,
% 9.91/10.10      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 9.91/10.10         ((k4_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62)
% 9.91/10.10           = (k3_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 9.91/10.10      inference('cnf', [status(esa)], [t73_enumset1])).
% 9.91/10.10  thf(t61_enumset1, axiom,
% 9.91/10.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 9.91/10.10     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 9.91/10.10       ( k2_xboole_0 @
% 9.91/10.10         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 9.91/10.10  thf('67', plain,
% 9.91/10.10      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 9.91/10.10         ((k5_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 9.91/10.10           = (k2_xboole_0 @ 
% 9.91/10.10              (k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38) @ 
% 9.91/10.10              (k1_tarski @ X39)))),
% 9.91/10.10      inference('cnf', [status(esa)], [t61_enumset1])).
% 9.91/10.10  thf('68', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 9.91/10.10         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 9.91/10.10           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 9.91/10.10              (k1_tarski @ X5)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['66', '67'])).
% 9.91/10.10  thf('69', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 9.91/10.10         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 9.91/10.10           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 9.91/10.10              (k1_tarski @ X0)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['65', '68'])).
% 9.91/10.10  thf(t72_enumset1, axiom,
% 9.91/10.10    (![A:$i,B:$i,C:$i,D:$i]:
% 9.91/10.10     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 9.91/10.10  thf('70', plain,
% 9.91/10.10      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 9.91/10.10         ((k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57)
% 9.91/10.10           = (k2_enumset1 @ X54 @ X55 @ X56 @ X57))),
% 9.91/10.10      inference('cnf', [status(esa)], [t72_enumset1])).
% 9.91/10.10  thf('71', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 9.91/10.10         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 9.91/10.10           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 9.91/10.10              (k1_tarski @ X0)))),
% 9.91/10.10      inference('demod', [status(thm)], ['69', '70'])).
% 9.91/10.10  thf('72', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.91/10.10         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 9.91/10.10           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['62', '71'])).
% 9.91/10.10  thf('73', plain,
% 9.91/10.10      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 9.91/10.10         ((k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57)
% 9.91/10.10           = (k2_enumset1 @ X54 @ X55 @ X56 @ X57))),
% 9.91/10.10      inference('cnf', [status(esa)], [t72_enumset1])).
% 9.91/10.10  thf('74', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.91/10.10         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 9.91/10.10           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 9.91/10.10      inference('demod', [status(thm)], ['72', '73'])).
% 9.91/10.10  thf('75', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 9.91/10.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 9.91/10.10      inference('sup+', [status(thm)], ['59', '74'])).
% 9.91/10.10  thf('76', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 9.91/10.10      inference('sup+', [status(thm)], ['60', '61'])).
% 9.91/10.10  thf('77', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]:
% 9.91/10.10         ((k2_tarski @ X0 @ X1)
% 9.91/10.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 9.91/10.10      inference('demod', [status(thm)], ['75', '76'])).
% 9.91/10.10  thf('78', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_A))),
% 9.91/10.10      inference('demod', [status(thm)], ['58', '77'])).
% 9.91/10.10  thf('79', plain,
% 9.91/10.10      (![X49 : $i, X50 : $i]:
% 9.91/10.10         ((k1_enumset1 @ X49 @ X49 @ X50) = (k2_tarski @ X49 @ X50))),
% 9.91/10.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 9.91/10.10  thf(d1_enumset1, axiom,
% 9.91/10.10    (![A:$i,B:$i,C:$i,D:$i]:
% 9.91/10.10     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 9.91/10.10       ( ![E:$i]:
% 9.91/10.10         ( ( r2_hidden @ E @ D ) <=>
% 9.91/10.10           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 9.91/10.10  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 9.91/10.10  thf(zf_stmt_2, axiom,
% 9.91/10.10    (![E:$i,C:$i,B:$i,A:$i]:
% 9.91/10.10     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 9.91/10.10       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 9.91/10.10  thf(zf_stmt_3, axiom,
% 9.91/10.10    (![A:$i,B:$i,C:$i,D:$i]:
% 9.91/10.10     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 9.91/10.10       ( ![E:$i]:
% 9.91/10.10         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 9.91/10.10  thf('80', plain,
% 9.91/10.10      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 9.91/10.10         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 9.91/10.10          | (r2_hidden @ X21 @ X25)
% 9.91/10.10          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 9.91/10.10      inference('cnf', [status(esa)], [zf_stmt_3])).
% 9.91/10.10  thf('81', plain,
% 9.91/10.10      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 9.91/10.10         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 9.91/10.10          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 9.91/10.10      inference('simplify', [status(thm)], ['80'])).
% 9.91/10.10  thf('82', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.91/10.10         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 9.91/10.10          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 9.91/10.10      inference('sup+', [status(thm)], ['79', '81'])).
% 9.91/10.10  thf('83', plain,
% 9.91/10.10      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 9.91/10.10         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 9.91/10.10      inference('cnf', [status(esa)], [zf_stmt_2])).
% 9.91/10.10  thf('84', plain,
% 9.91/10.10      (![X16 : $i, X18 : $i, X19 : $i]:
% 9.91/10.10         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 9.91/10.10      inference('simplify', [status(thm)], ['83'])).
% 9.91/10.10  thf('85', plain,
% 9.91/10.10      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 9.91/10.10      inference('sup-', [status(thm)], ['82', '84'])).
% 9.91/10.10  thf('86', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 9.91/10.10      inference('sup+', [status(thm)], ['78', '85'])).
% 9.91/10.10  thf(d1_tarski, axiom,
% 9.91/10.10    (![A:$i,B:$i]:
% 9.91/10.10     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 9.91/10.10       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 9.91/10.10  thf('87', plain,
% 9.91/10.10      (![X28 : $i, X30 : $i, X31 : $i]:
% 9.91/10.10         (~ (r2_hidden @ X31 @ X30)
% 9.91/10.10          | ((X31) = (X28))
% 9.91/10.10          | ((X30) != (k1_tarski @ X28)))),
% 9.91/10.10      inference('cnf', [status(esa)], [d1_tarski])).
% 9.91/10.10  thf('88', plain,
% 9.91/10.10      (![X28 : $i, X31 : $i]:
% 9.91/10.10         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 9.91/10.10      inference('simplify', [status(thm)], ['87'])).
% 9.91/10.10  thf('89', plain, (((sk_B) = (sk_A))),
% 9.91/10.10      inference('sup-', [status(thm)], ['86', '88'])).
% 9.91/10.10  thf('90', plain, (((sk_A) != (sk_B))),
% 9.91/10.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.91/10.10  thf('91', plain, ($false),
% 9.91/10.10      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 9.91/10.10  
% 9.91/10.10  % SZS output end Refutation
% 9.91/10.10  
% 9.91/10.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
