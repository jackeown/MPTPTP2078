%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FGIYWJvvXM

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:21 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 732 expanded)
%              Number of leaves         :   26 ( 246 expanded)
%              Depth                    :   39
%              Number of atoms          : 1245 (6245 expanded)
%              Number of equality atoms :  130 ( 700 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('13',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_xboole_0 @ X46 @ ( k1_tarski @ X45 ) )
        = ( k1_tarski @ X45 ) )
      | ~ ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('20',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('27',plain,
    ( ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf('37',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['23','36'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','40','43'])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('50',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('51',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('54',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['48','54'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','55'])).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) )
        = ( k4_xboole_0 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('60',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('61',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['58','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['7','66'])).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
        = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
        = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
        = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('82',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','88'])).

thf('90',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','89'])).

thf('91',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('92',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('93',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','88','92'])).

thf('94',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('106',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('108',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('110',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('112',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('117',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('118',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['116','117'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('119',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('120',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( r2_hidden @ X49 @ X50 )
      | ~ ( r1_tarski @ ( k2_tarski @ X49 @ X51 ) @ X50 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['90','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FGIYWJvvXM
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 803 iterations in 0.380s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.61/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.81  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(t68_zfmisc_1, conjecture,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.61/0.81       ( r2_hidden @ A @ B ) ))).
% 0.61/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.81    (~( ![A:$i,B:$i]:
% 0.61/0.81        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.61/0.81          ( r2_hidden @ A @ B ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.61/0.81  thf('0', plain,
% 0.61/0.81      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.61/0.81        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('1', plain,
% 0.61/0.81      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('split', [status(esa)], ['0'])).
% 0.61/0.81  thf('2', plain,
% 0.61/0.81      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.61/0.81       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.61/0.81      inference('split', [status(esa)], ['0'])).
% 0.61/0.81  thf(commutativity_k2_tarski, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.61/0.81  thf('3', plain,
% 0.61/0.81      (![X15 : $i, X16 : $i]:
% 0.61/0.81         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.61/0.81  thf(l51_zfmisc_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('4', plain,
% 0.61/0.81      (![X47 : $i, X48 : $i]:
% 0.61/0.81         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.61/0.81      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.61/0.81  thf('5', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['3', '4'])).
% 0.61/0.81  thf('6', plain,
% 0.61/0.81      (![X47 : $i, X48 : $i]:
% 0.61/0.81         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.61/0.81      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.61/0.81  thf('7', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['5', '6'])).
% 0.61/0.81  thf(t95_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k3_xboole_0 @ A @ B ) =
% 0.61/0.81       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.61/0.81  thf('8', plain,
% 0.61/0.81      (![X13 : $i, X14 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X13 @ X14)
% 0.61/0.81           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 0.61/0.81              (k2_xboole_0 @ X13 @ X14)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.61/0.81  thf(t91_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.81       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.61/0.81  thf('9', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.61/0.81           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.81  thf('10', plain,
% 0.61/0.81      (![X13 : $i, X14 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X13 @ X14)
% 0.61/0.81           = (k5_xboole_0 @ X13 @ 
% 0.61/0.81              (k5_xboole_0 @ X14 @ (k2_xboole_0 @ X13 @ X14))))),
% 0.61/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.81  thf('11', plain,
% 0.61/0.81      (((r2_hidden @ sk_A @ sk_B)
% 0.61/0.81        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('12', plain,
% 0.61/0.81      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('split', [status(esa)], ['11'])).
% 0.61/0.81  thf(l31_zfmisc_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r2_hidden @ A @ B ) =>
% 0.61/0.81       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.61/0.81  thf('13', plain,
% 0.61/0.81      (![X45 : $i, X46 : $i]:
% 0.61/0.81         (((k3_xboole_0 @ X46 @ (k1_tarski @ X45)) = (k1_tarski @ X45))
% 0.61/0.81          | ~ (r2_hidden @ X45 @ X46))),
% 0.61/0.81      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.61/0.81  thf('14', plain,
% 0.61/0.81      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.81  thf(t100_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.81  thf('15', plain,
% 0.61/0.81      (![X4 : $i, X5 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X4 @ X5)
% 0.61/0.81           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.81  thf('16', plain,
% 0.61/0.81      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.61/0.81          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['14', '15'])).
% 0.61/0.81  thf('17', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.61/0.81           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.81  thf('18', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.61/0.81            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['16', '17'])).
% 0.61/0.81  thf('19', plain,
% 0.61/0.81      (![X13 : $i, X14 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X13 @ X14)
% 0.61/0.81           = (k5_xboole_0 @ X13 @ 
% 0.61/0.81              (k5_xboole_0 @ X14 @ (k2_xboole_0 @ X13 @ X14))))),
% 0.61/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.81  thf('20', plain,
% 0.61/0.81      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.61/0.81          = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.61/0.81             (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.81  thf('21', plain,
% 0.61/0.81      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.81  thf(commutativity_k5_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.61/0.81  thf('22', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf('23', plain,
% 0.61/0.81      ((((k1_tarski @ sk_A)
% 0.61/0.81          = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.61/0.81             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.61/0.81  thf('24', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf(t92_xboole_1, axiom,
% 0.61/0.81    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.61/0.81  thf('25', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.61/0.81      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.81  thf('26', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.61/0.81            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['16', '17'])).
% 0.61/0.81  thf('27', plain,
% 0.61/0.81      ((((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.61/0.81          (k1_tarski @ sk_A)) = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['25', '26'])).
% 0.61/0.81  thf('28', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf('29', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf('30', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf(t5_boole, axiom,
% 0.61/0.81    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.81  thf('31', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.61/0.81      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.81  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.81  thf('33', plain,
% 0.61/0.81      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.61/0.81          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['27', '28', '29', '32'])).
% 0.61/0.81  thf('34', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.61/0.81           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.81  thf('35', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ sk_B @ X0)
% 0.61/0.81            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.61/0.81               (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['33', '34'])).
% 0.61/0.81  thf('36', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ sk_B @ X0)
% 0.61/0.81            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.61/0.81               (k5_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['24', '35'])).
% 0.61/0.81  thf('37', plain,
% 0.61/0.81      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.61/0.81          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['23', '36'])).
% 0.61/0.81  thf(idempotence_k3_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.61/0.81  thf('38', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.61/0.81      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.61/0.81  thf('39', plain,
% 0.61/0.81      (![X4 : $i, X5 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X4 @ X5)
% 0.61/0.81           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.81  thf('40', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['38', '39'])).
% 0.61/0.81  thf('41', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['38', '39'])).
% 0.61/0.81  thf('42', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.61/0.81      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.81  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['41', '42'])).
% 0.61/0.81  thf('44', plain,
% 0.61/0.81      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.61/0.81          = (k1_xboole_0)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['37', '40', '43'])).
% 0.61/0.81  thf('45', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.61/0.81           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.81  thf('46', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.61/0.81            = (k5_xboole_0 @ sk_B @ 
% 0.61/0.81               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['44', '45'])).
% 0.61/0.81  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.81  thf('48', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((X0)
% 0.61/0.81            = (k5_xboole_0 @ sk_B @ 
% 0.61/0.81               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['46', '47'])).
% 0.61/0.81  thf('49', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.61/0.81      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.81  thf('50', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((X0)
% 0.61/0.81            = (k5_xboole_0 @ sk_B @ 
% 0.61/0.81               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['46', '47'])).
% 0.61/0.81  thf('51', plain,
% 0.61/0.81      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.61/0.81          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['49', '50'])).
% 0.61/0.81  thf('52', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.81  thf('54', plain,
% 0.61/0.81      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.61/0.81  thf('55', plain,
% 0.61/0.81      ((![X0 : $i]: ((X0) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['48', '54'])).
% 0.61/0.81  thf('56', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0))
% 0.61/0.81            = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['10', '55'])).
% 0.61/0.81  thf('57', plain,
% 0.61/0.81      (![X4 : $i, X5 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X4 @ X5)
% 0.61/0.81           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.81  thf('58', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0))
% 0.61/0.81            = (k4_xboole_0 @ sk_B @ X0)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['56', '57'])).
% 0.61/0.81  thf('59', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf('60', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.61/0.81      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.81  thf('61', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.61/0.81           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.81  thf('62', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.61/0.81           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['60', '61'])).
% 0.61/0.81  thf('63', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.81  thf('64', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.81  thf('65', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['59', '64'])).
% 0.61/0.81  thf('66', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((X0)
% 0.61/0.81            = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ 
% 0.61/0.81               (k4_xboole_0 @ sk_B @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['58', '65'])).
% 0.61/0.81  thf('67', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((X0)
% 0.61/0.81            = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ 
% 0.61/0.81               (k4_xboole_0 @ sk_B @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['7', '66'])).
% 0.61/0.81  thf('68', plain,
% 0.61/0.81      (![X13 : $i, X14 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X13 @ X14)
% 0.61/0.81           = (k5_xboole_0 @ X13 @ 
% 0.61/0.81              (k5_xboole_0 @ X14 @ (k2_xboole_0 @ X13 @ X14))))),
% 0.61/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.81  thf('69', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.61/0.81           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.81  thf('70', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.61/0.81           = (k5_xboole_0 @ X1 @ 
% 0.61/0.81              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X2)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['68', '69'])).
% 0.61/0.81  thf('71', plain,
% 0.61/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.61/0.81           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.81  thf('72', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.61/0.81           = (k5_xboole_0 @ X1 @ 
% 0.61/0.81              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 0.61/0.81      inference('demod', [status(thm)], ['70', '71'])).
% 0.61/0.81  thf('73', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ sk_B @ X0))
% 0.61/0.81            = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['67', '72'])).
% 0.61/0.81  thf('74', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf('75', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['59', '64'])).
% 0.61/0.81  thf('76', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ (k3_xboole_0 @ X0 @ sk_B))
% 0.61/0.81            = (sk_B)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.61/0.81  thf('77', plain,
% 0.61/0.81      (![X4 : $i, X5 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X4 @ X5)
% 0.61/0.81           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.81  thf('78', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.61/0.81            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['16', '17'])).
% 0.61/0.81  thf('79', plain,
% 0.61/0.81      ((![X0 : $i]:
% 0.61/0.81          ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.61/0.81            (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.61/0.81            = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['77', '78'])).
% 0.61/0.81  thf('80', plain,
% 0.61/0.81      ((((sk_B)
% 0.61/0.81          = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['76', '79'])).
% 0.61/0.81  thf('81', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.81  thf('82', plain,
% 0.61/0.81      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.61/0.81          = (k5_xboole_0 @ sk_B @ sk_B)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['80', '81'])).
% 0.61/0.81  thf('83', plain,
% 0.61/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['38', '39'])).
% 0.61/0.81  thf('84', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['41', '42'])).
% 0.61/0.81  thf('85', plain,
% 0.61/0.81      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.61/0.81         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.61/0.81  thf('86', plain,
% 0.61/0.81      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.61/0.81         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.61/0.81      inference('split', [status(esa)], ['0'])).
% 0.61/0.81  thf('87', plain,
% 0.61/0.81      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.61/0.81         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.61/0.81             ((r2_hidden @ sk_A @ sk_B)))),
% 0.61/0.81      inference('sup-', [status(thm)], ['85', '86'])).
% 0.61/0.81  thf('88', plain,
% 0.61/0.81      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.61/0.81       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.61/0.81      inference('simplify', [status(thm)], ['87'])).
% 0.61/0.81  thf('89', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.61/0.81      inference('sat_resolution*', [status(thm)], ['2', '88'])).
% 0.61/0.81  thf('90', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.61/0.81      inference('simpl_trail', [status(thm)], ['1', '89'])).
% 0.61/0.81  thf('91', plain,
% 0.61/0.81      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.61/0.81         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.61/0.81      inference('split', [status(esa)], ['11'])).
% 0.61/0.81  thf('92', plain,
% 0.61/0.81      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.61/0.81       ((r2_hidden @ sk_A @ sk_B))),
% 0.61/0.81      inference('split', [status(esa)], ['11'])).
% 0.61/0.81  thf('93', plain,
% 0.61/0.81      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.61/0.81      inference('sat_resolution*', [status(thm)], ['2', '88', '92'])).
% 0.61/0.81  thf('94', plain,
% 0.61/0.81      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.61/0.81      inference('simpl_trail', [status(thm)], ['91', '93'])).
% 0.61/0.81  thf('95', plain,
% 0.61/0.81      (![X13 : $i, X14 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X13 @ X14)
% 0.61/0.81           = (k5_xboole_0 @ X13 @ 
% 0.61/0.81              (k5_xboole_0 @ X14 @ (k2_xboole_0 @ X13 @ X14))))),
% 0.61/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.61/0.81  thf('96', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.81  thf('97', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['95', '96'])).
% 0.61/0.81  thf('98', plain,
% 0.61/0.81      (![X4 : $i, X5 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X4 @ X5)
% 0.61/0.81           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.81  thf('99', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k4_xboole_0 @ X1 @ X0))),
% 0.61/0.81      inference('demod', [status(thm)], ['97', '98'])).
% 0.61/0.81  thf('100', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.81  thf('101', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X1 @ X0)
% 0.61/0.81           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['99', '100'])).
% 0.61/0.81  thf('102', plain,
% 0.61/0.81      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.61/0.81         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['94', '101'])).
% 0.61/0.81  thf('103', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['5', '6'])).
% 0.61/0.81  thf('104', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf('105', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.81  thf('106', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.61/0.81      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 0.61/0.81  thf('107', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k4_xboole_0 @ X1 @ X0))),
% 0.61/0.81      inference('demod', [status(thm)], ['97', '98'])).
% 0.61/0.81  thf('108', plain,
% 0.61/0.81      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.61/0.81         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['106', '107'])).
% 0.61/0.81  thf('109', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.61/0.81  thf('110', plain,
% 0.61/0.81      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.61/0.81         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.61/0.81      inference('demod', [status(thm)], ['108', '109'])).
% 0.61/0.81  thf('111', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.81  thf('112', plain,
% 0.61/0.81      (((k1_tarski @ sk_A)
% 0.61/0.81         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.61/0.81      inference('sup+', [status(thm)], ['110', '111'])).
% 0.61/0.81  thf('113', plain,
% 0.61/0.81      (![X4 : $i, X5 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X4 @ X5)
% 0.61/0.81           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.81  thf('114', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.61/0.81  thf('115', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X1 @ X0)
% 0.61/0.81           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['113', '114'])).
% 0.61/0.81  thf('116', plain,
% 0.61/0.81      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.61/0.81      inference('demod', [status(thm)], ['112', '115'])).
% 0.61/0.81  thf(t17_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.81  thf('117', plain,
% 0.61/0.81      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.61/0.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.61/0.81  thf('118', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.61/0.81      inference('sup+', [status(thm)], ['116', '117'])).
% 0.61/0.81  thf(t69_enumset1, axiom,
% 0.61/0.81    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.61/0.81  thf('119', plain,
% 0.61/0.81      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.81  thf(t38_zfmisc_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.61/0.81       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.61/0.81  thf('120', plain,
% 0.61/0.81      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.61/0.81         ((r2_hidden @ X49 @ X50)
% 0.61/0.81          | ~ (r1_tarski @ (k2_tarski @ X49 @ X51) @ X50))),
% 0.61/0.81      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.61/0.81  thf('121', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.61/0.81      inference('sup-', [status(thm)], ['119', '120'])).
% 0.61/0.81  thf('122', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.61/0.81      inference('sup-', [status(thm)], ['118', '121'])).
% 0.61/0.81  thf('123', plain, ($false), inference('demod', [status(thm)], ['90', '122'])).
% 0.61/0.81  
% 0.61/0.81  % SZS output end Refutation
% 0.61/0.81  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
