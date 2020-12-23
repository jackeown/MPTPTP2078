%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Shr3gyuxkI

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:12 EST 2020

% Result     : Theorem 8.83s
% Output     : Refutation 8.83s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 324 expanded)
%              Number of leaves         :   39 ( 120 expanded)
%              Depth                    :   21
%              Number of atoms          : 1034 (2341 expanded)
%              Number of equality atoms :  117 ( 285 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','25'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('43',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','53','54'])).

thf('56',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['45','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','58'])).

thf('60',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['43','59'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('61',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('62',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('65',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('66',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('69',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k5_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('72',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['64','73'])).

thf('75',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['60','79'])).

thf('81',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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

thf('82',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('83',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('86',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['80','87'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('89',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('90',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Shr3gyuxkI
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 8.83/9.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.83/9.00  % Solved by: fo/fo7.sh
% 8.83/9.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.83/9.00  % done 6928 iterations in 8.558s
% 8.83/9.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.83/9.00  % SZS output start Refutation
% 8.83/9.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.83/9.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.83/9.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 8.83/9.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.83/9.00  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.83/9.00  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 8.83/9.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.83/9.00  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 8.83/9.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.83/9.00  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 8.83/9.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.83/9.00  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 8.83/9.00  thf(sk_A_type, type, sk_A: $i).
% 8.83/9.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.83/9.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 8.83/9.00  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 8.83/9.00  thf(sk_B_type, type, sk_B: $i).
% 8.83/9.00  thf(t13_zfmisc_1, conjecture,
% 8.83/9.00    (![A:$i,B:$i]:
% 8.83/9.00     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 8.83/9.00         ( k1_tarski @ A ) ) =>
% 8.83/9.00       ( ( A ) = ( B ) ) ))).
% 8.83/9.00  thf(zf_stmt_0, negated_conjecture,
% 8.83/9.00    (~( ![A:$i,B:$i]:
% 8.83/9.00        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 8.83/9.00            ( k1_tarski @ A ) ) =>
% 8.83/9.00          ( ( A ) = ( B ) ) ) )),
% 8.83/9.00    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 8.83/9.00  thf('0', plain,
% 8.83/9.00      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 8.83/9.00         = (k1_tarski @ sk_A))),
% 8.83/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.83/9.00  thf(t98_xboole_1, axiom,
% 8.83/9.00    (![A:$i,B:$i]:
% 8.83/9.00     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 8.83/9.00  thf('1', plain,
% 8.83/9.00      (![X14 : $i, X15 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ X14 @ X15)
% 8.83/9.00           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 8.83/9.00      inference('cnf', [status(esa)], [t98_xboole_1])).
% 8.83/9.00  thf(idempotence_k3_xboole_0, axiom,
% 8.83/9.00    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 8.83/9.00  thf('2', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 8.83/9.00      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 8.83/9.00  thf(t100_xboole_1, axiom,
% 8.83/9.00    (![A:$i,B:$i]:
% 8.83/9.00     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.83/9.00  thf('3', plain,
% 8.83/9.00      (![X3 : $i, X4 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X3 @ X4)
% 8.83/9.00           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 8.83/9.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.83/9.00  thf('4', plain,
% 8.83/9.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['2', '3'])).
% 8.83/9.00  thf(t91_xboole_1, axiom,
% 8.83/9.00    (![A:$i,B:$i,C:$i]:
% 8.83/9.00     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 8.83/9.00       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 8.83/9.00  thf('5', plain,
% 8.83/9.00      (![X11 : $i, X12 : $i, X13 : $i]:
% 8.83/9.00         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 8.83/9.00           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 8.83/9.00      inference('cnf', [status(esa)], [t91_xboole_1])).
% 8.83/9.00  thf('6', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 8.83/9.00           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['4', '5'])).
% 8.83/9.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 8.83/9.00  thf('7', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 8.83/9.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 8.83/9.00  thf(t28_xboole_1, axiom,
% 8.83/9.00    (![A:$i,B:$i]:
% 8.83/9.00     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 8.83/9.00  thf('8', plain,
% 8.83/9.00      (![X5 : $i, X6 : $i]:
% 8.83/9.00         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 8.83/9.00      inference('cnf', [status(esa)], [t28_xboole_1])).
% 8.83/9.00  thf('9', plain,
% 8.83/9.00      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.83/9.00      inference('sup-', [status(thm)], ['7', '8'])).
% 8.83/9.00  thf(commutativity_k3_xboole_0, axiom,
% 8.83/9.00    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 8.83/9.00  thf('10', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.83/9.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.83/9.00  thf('11', plain,
% 8.83/9.00      (![X3 : $i, X4 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X3 @ X4)
% 8.83/9.00           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 8.83/9.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.83/9.00  thf('12', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X0 @ X1)
% 8.83/9.00           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['10', '11'])).
% 8.83/9.00  thf('13', plain,
% 8.83/9.00      (![X0 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['9', '12'])).
% 8.83/9.00  thf(t5_boole, axiom,
% 8.83/9.00    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.83/9.00  thf('14', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 8.83/9.00      inference('cnf', [status(esa)], [t5_boole])).
% 8.83/9.00  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['13', '14'])).
% 8.83/9.00  thf(t48_xboole_1, axiom,
% 8.83/9.00    (![A:$i,B:$i]:
% 8.83/9.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.83/9.00  thf('16', plain,
% 8.83/9.00      (![X8 : $i, X9 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 8.83/9.00           = (k3_xboole_0 @ X8 @ X9))),
% 8.83/9.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.83/9.00  thf('17', plain,
% 8.83/9.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['15', '16'])).
% 8.83/9.00  thf('18', plain,
% 8.83/9.00      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.83/9.00      inference('sup-', [status(thm)], ['7', '8'])).
% 8.83/9.00  thf('19', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.83/9.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.83/9.00  thf('20', plain,
% 8.83/9.00      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['18', '19'])).
% 8.83/9.00  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.83/9.00      inference('demod', [status(thm)], ['17', '20'])).
% 8.83/9.00  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['13', '14'])).
% 8.83/9.00  thf('23', plain,
% 8.83/9.00      (![X14 : $i, X15 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ X14 @ X15)
% 8.83/9.00           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 8.83/9.00      inference('cnf', [status(esa)], [t98_xboole_1])).
% 8.83/9.00  thf('24', plain,
% 8.83/9.00      (![X0 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['22', '23'])).
% 8.83/9.00  thf('25', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ k1_xboole_0 @ X1)
% 8.83/9.00           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 8.83/9.00      inference('sup+', [status(thm)], ['21', '24'])).
% 8.83/9.00  thf('26', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ k1_xboole_0 @ X1)
% 8.83/9.00           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 8.83/9.00      inference('demod', [status(thm)], ['6', '25'])).
% 8.83/9.00  thf('27', plain,
% 8.83/9.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['2', '3'])).
% 8.83/9.00  thf('28', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ k1_xboole_0 @ X1)
% 8.83/9.00           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 8.83/9.00      inference('demod', [status(thm)], ['6', '25'])).
% 8.83/9.00  thf('29', plain,
% 8.83/9.00      (![X0 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 8.83/9.00           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['27', '28'])).
% 8.83/9.00  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.83/9.00      inference('demod', [status(thm)], ['17', '20'])).
% 8.83/9.00  thf('31', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 8.83/9.00      inference('cnf', [status(esa)], [t5_boole])).
% 8.83/9.00  thf('32', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 8.83/9.00      inference('sup+', [status(thm)], ['30', '31'])).
% 8.83/9.00  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.83/9.00      inference('demod', [status(thm)], ['29', '32'])).
% 8.83/9.00  thf('34', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 8.83/9.00      inference('demod', [status(thm)], ['26', '33'])).
% 8.83/9.00  thf('35', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X0 @ X1)
% 8.83/9.00           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['1', '34'])).
% 8.83/9.00  thf('36', plain,
% 8.83/9.00      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 8.83/9.00         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['0', '35'])).
% 8.83/9.00  thf('37', plain,
% 8.83/9.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['2', '3'])).
% 8.83/9.00  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.83/9.00      inference('demod', [status(thm)], ['17', '20'])).
% 8.83/9.00  thf('39', plain,
% 8.83/9.00      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 8.83/9.00      inference('demod', [status(thm)], ['36', '37', '38'])).
% 8.83/9.00  thf('40', plain,
% 8.83/9.00      (![X8 : $i, X9 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 8.83/9.00           = (k3_xboole_0 @ X8 @ X9))),
% 8.83/9.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.83/9.00  thf('41', plain,
% 8.83/9.00      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 8.83/9.00         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['39', '40'])).
% 8.83/9.00  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['13', '14'])).
% 8.83/9.00  thf('43', plain,
% 8.83/9.00      (((k1_tarski @ sk_B)
% 8.83/9.00         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 8.83/9.00      inference('demod', [status(thm)], ['41', '42'])).
% 8.83/9.00  thf('44', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.83/9.00      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.83/9.00  thf('45', plain,
% 8.83/9.00      (![X8 : $i, X9 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 8.83/9.00           = (k3_xboole_0 @ X8 @ X9))),
% 8.83/9.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.83/9.00  thf('46', plain,
% 8.83/9.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['2', '3'])).
% 8.83/9.00  thf('47', plain,
% 8.83/9.00      (![X3 : $i, X4 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X3 @ X4)
% 8.83/9.00           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 8.83/9.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.83/9.00  thf('48', plain,
% 8.83/9.00      (![X11 : $i, X12 : $i, X13 : $i]:
% 8.83/9.00         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 8.83/9.00           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 8.83/9.00      inference('cnf', [status(esa)], [t91_xboole_1])).
% 8.83/9.00  thf('49', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.83/9.00         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 8.83/9.00           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['47', '48'])).
% 8.83/9.00  thf('50', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 8.83/9.00           = (k5_xboole_0 @ X1 @ 
% 8.83/9.00              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 8.83/9.00      inference('sup+', [status(thm)], ['46', '49'])).
% 8.83/9.00  thf('51', plain,
% 8.83/9.00      (![X8 : $i, X9 : $i]:
% 8.83/9.00         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 8.83/9.00           = (k3_xboole_0 @ X8 @ X9))),
% 8.83/9.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.83/9.00  thf('52', plain,
% 8.83/9.00      (![X14 : $i, X15 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ X14 @ X15)
% 8.83/9.00           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 8.83/9.00      inference('cnf', [status(esa)], [t98_xboole_1])).
% 8.83/9.00  thf('53', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 8.83/9.00           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['51', '52'])).
% 8.83/9.00  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.83/9.00      inference('demod', [status(thm)], ['17', '20'])).
% 8.83/9.00  thf('55', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 8.83/9.00           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 8.83/9.00      inference('demod', [status(thm)], ['50', '53', '54'])).
% 8.83/9.00  thf('56', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 8.83/9.00      inference('cnf', [status(esa)], [t5_boole])).
% 8.83/9.00  thf('57', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 8.83/9.00      inference('demod', [status(thm)], ['55', '56'])).
% 8.83/9.00  thf('58', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 8.83/9.00      inference('sup+', [status(thm)], ['45', '57'])).
% 8.83/9.00  thf('59', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['44', '58'])).
% 8.83/9.00  thf('60', plain,
% 8.83/9.00      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 8.83/9.00         = (k1_tarski @ sk_A))),
% 8.83/9.00      inference('sup+', [status(thm)], ['43', '59'])).
% 8.83/9.00  thf(t69_enumset1, axiom,
% 8.83/9.00    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 8.83/9.00  thf('61', plain,
% 8.83/9.00      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 8.83/9.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.83/9.00  thf(t71_enumset1, axiom,
% 8.83/9.00    (![A:$i,B:$i,C:$i]:
% 8.83/9.00     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 8.83/9.00  thf('62', plain,
% 8.83/9.00      (![X43 : $i, X44 : $i, X45 : $i]:
% 8.83/9.00         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 8.83/9.00           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 8.83/9.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.83/9.00  thf(t70_enumset1, axiom,
% 8.83/9.00    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 8.83/9.00  thf('63', plain,
% 8.83/9.00      (![X41 : $i, X42 : $i]:
% 8.83/9.00         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 8.83/9.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.83/9.00  thf('64', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['62', '63'])).
% 8.83/9.00  thf(t74_enumset1, axiom,
% 8.83/9.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.83/9.00     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 8.83/9.00       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 8.83/9.00  thf('65', plain,
% 8.83/9.00      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 8.83/9.00         ((k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 8.83/9.00           = (k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 8.83/9.00      inference('cnf', [status(esa)], [t74_enumset1])).
% 8.83/9.00  thf(t73_enumset1, axiom,
% 8.83/9.00    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.83/9.00     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 8.83/9.00       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 8.83/9.00  thf('66', plain,
% 8.83/9.00      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 8.83/9.00         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 8.83/9.00           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 8.83/9.00      inference('cnf', [status(esa)], [t73_enumset1])).
% 8.83/9.00  thf('67', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.83/9.00         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 8.83/9.00           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['65', '66'])).
% 8.83/9.00  thf('68', plain,
% 8.83/9.00      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 8.83/9.00         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 8.83/9.00           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 8.83/9.00      inference('cnf', [status(esa)], [t73_enumset1])).
% 8.83/9.00  thf(t61_enumset1, axiom,
% 8.83/9.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 8.83/9.00     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 8.83/9.00       ( k2_xboole_0 @
% 8.83/9.00         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 8.83/9.00  thf('69', plain,
% 8.83/9.00      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 8.83/9.00         ((k5_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 8.83/9.00           = (k2_xboole_0 @ 
% 8.83/9.00              (k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38) @ 
% 8.83/9.00              (k1_tarski @ X39)))),
% 8.83/9.00      inference('cnf', [status(esa)], [t61_enumset1])).
% 8.83/9.00  thf('70', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.83/9.00         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 8.83/9.00           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 8.83/9.00              (k1_tarski @ X5)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['68', '69'])).
% 8.83/9.00  thf('71', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.83/9.00         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 8.83/9.00           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 8.83/9.00              (k1_tarski @ X0)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['67', '70'])).
% 8.83/9.00  thf(t72_enumset1, axiom,
% 8.83/9.00    (![A:$i,B:$i,C:$i,D:$i]:
% 8.83/9.00     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 8.83/9.00  thf('72', plain,
% 8.83/9.00      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 8.83/9.00         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 8.83/9.00           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 8.83/9.00      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.83/9.00  thf('73', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.83/9.00         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 8.83/9.00           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 8.83/9.00              (k1_tarski @ X0)))),
% 8.83/9.00      inference('demod', [status(thm)], ['71', '72'])).
% 8.83/9.00  thf('74', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.83/9.00         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 8.83/9.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['64', '73'])).
% 8.83/9.00  thf('75', plain,
% 8.83/9.00      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 8.83/9.00         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 8.83/9.00           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 8.83/9.00      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.83/9.00  thf('76', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.83/9.00         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 8.83/9.00           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 8.83/9.00      inference('demod', [status(thm)], ['74', '75'])).
% 8.83/9.00  thf('77', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 8.83/9.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 8.83/9.00      inference('sup+', [status(thm)], ['61', '76'])).
% 8.83/9.00  thf('78', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 8.83/9.00      inference('sup+', [status(thm)], ['62', '63'])).
% 8.83/9.00  thf('79', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]:
% 8.83/9.00         ((k2_tarski @ X0 @ X1)
% 8.83/9.00           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 8.83/9.00      inference('demod', [status(thm)], ['77', '78'])).
% 8.83/9.00  thf('80', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_A))),
% 8.83/9.00      inference('demod', [status(thm)], ['60', '79'])).
% 8.83/9.00  thf('81', plain,
% 8.83/9.00      (![X41 : $i, X42 : $i]:
% 8.83/9.00         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 8.83/9.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.83/9.00  thf(d1_enumset1, axiom,
% 8.83/9.00    (![A:$i,B:$i,C:$i,D:$i]:
% 8.83/9.00     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 8.83/9.00       ( ![E:$i]:
% 8.83/9.00         ( ( r2_hidden @ E @ D ) <=>
% 8.83/9.00           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 8.83/9.00  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 8.83/9.00  thf(zf_stmt_2, axiom,
% 8.83/9.00    (![E:$i,C:$i,B:$i,A:$i]:
% 8.83/9.00     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 8.83/9.00       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 8.83/9.00  thf(zf_stmt_3, axiom,
% 8.83/9.00    (![A:$i,B:$i,C:$i,D:$i]:
% 8.83/9.00     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 8.83/9.00       ( ![E:$i]:
% 8.83/9.00         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 8.83/9.00  thf('82', plain,
% 8.83/9.00      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 8.83/9.00         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 8.83/9.00          | (r2_hidden @ X21 @ X25)
% 8.83/9.00          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 8.83/9.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 8.83/9.00  thf('83', plain,
% 8.83/9.00      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 8.83/9.00         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 8.83/9.00          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 8.83/9.00      inference('simplify', [status(thm)], ['82'])).
% 8.83/9.00  thf('84', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.83/9.00         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 8.83/9.00          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 8.83/9.00      inference('sup+', [status(thm)], ['81', '83'])).
% 8.83/9.00  thf('85', plain,
% 8.83/9.00      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 8.83/9.00         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 8.83/9.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 8.83/9.00  thf('86', plain,
% 8.83/9.00      (![X16 : $i, X18 : $i, X19 : $i]:
% 8.83/9.00         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 8.83/9.00      inference('simplify', [status(thm)], ['85'])).
% 8.83/9.00  thf('87', plain,
% 8.83/9.00      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 8.83/9.00      inference('sup-', [status(thm)], ['84', '86'])).
% 8.83/9.00  thf('88', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 8.83/9.00      inference('sup+', [status(thm)], ['80', '87'])).
% 8.83/9.00  thf(d1_tarski, axiom,
% 8.83/9.00    (![A:$i,B:$i]:
% 8.83/9.00     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 8.83/9.00       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 8.83/9.00  thf('89', plain,
% 8.83/9.00      (![X28 : $i, X30 : $i, X31 : $i]:
% 8.83/9.00         (~ (r2_hidden @ X31 @ X30)
% 8.83/9.00          | ((X31) = (X28))
% 8.83/9.00          | ((X30) != (k1_tarski @ X28)))),
% 8.83/9.00      inference('cnf', [status(esa)], [d1_tarski])).
% 8.83/9.00  thf('90', plain,
% 8.83/9.00      (![X28 : $i, X31 : $i]:
% 8.83/9.00         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 8.83/9.00      inference('simplify', [status(thm)], ['89'])).
% 8.83/9.00  thf('91', plain, (((sk_B) = (sk_A))),
% 8.83/9.00      inference('sup-', [status(thm)], ['88', '90'])).
% 8.83/9.00  thf('92', plain, (((sk_A) != (sk_B))),
% 8.83/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.83/9.00  thf('93', plain, ($false),
% 8.83/9.00      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 8.83/9.00  
% 8.83/9.00  % SZS output end Refutation
% 8.83/9.00  
% 8.83/9.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
