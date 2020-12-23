%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BnE1w13E3X

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:21 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  215 (9428 expanded)
%              Number of leaves         :   26 (3036 expanded)
%              Depth                    :   52
%              Number of atoms          : 2073 (85695 expanded)
%              Number of equality atoms :  201 (9051 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k3_xboole_0 @ X51 @ ( k1_tarski @ X50 ) )
        = ( k1_tarski @ X50 ) )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('10',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('12',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('14',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('16',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('49',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('51',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','49','50'])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('53',plain,
    ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('55',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('57',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('60',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54','60'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('63',plain,
    ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('65',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','49','50'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('68',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('69',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('71',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('73',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('75',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('78',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('80',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('83',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('84',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('87',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['82','85','88'])).

thf('90',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','92'])).

thf('94',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','93'])).

thf('95',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('96',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('97',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','92','96'])).

thf('98',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('100',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('101',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('109',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('117',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('118',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['115','116','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('124',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('126',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['95','97'])).

thf('127',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('128',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('132',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('134',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('135',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','136'])).

thf('138',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('139',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','136'])).

thf('141',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('143',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('146',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','136'])).

thf('150',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('151',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['152','155'])).

thf('157',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['149','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['148','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['125','158'])).

thf('160',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['159','162'])).

thf('164',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['148','157'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('174',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['124','169','170','171','172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('176',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('178',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('179',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('181',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('183',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('184',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ( ( k3_xboole_0 @ X49 @ ( k1_tarski @ X48 ) )
       != ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('185',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    $false ),
    inference(demod,[status(thm)],['94','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BnE1w13E3X
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:58:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.77/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/1.01  % Solved by: fo/fo7.sh
% 0.77/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/1.01  % done 993 iterations in 0.557s
% 0.77/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/1.01  % SZS output start Refutation
% 0.77/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/1.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.77/1.01  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.77/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.77/1.01  thf(t68_zfmisc_1, conjecture,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.77/1.01       ( r2_hidden @ A @ B ) ))).
% 0.77/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.77/1.01    (~( ![A:$i,B:$i]:
% 0.77/1.01        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.77/1.01          ( r2_hidden @ A @ B ) ) )),
% 0.77/1.01    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.77/1.01  thf('0', plain,
% 0.77/1.01      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.77/1.01        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('1', plain,
% 0.77/1.01      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('split', [status(esa)], ['0'])).
% 0.77/1.01  thf('2', plain,
% 0.77/1.01      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.77/1.01       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.77/1.01      inference('split', [status(esa)], ['0'])).
% 0.77/1.01  thf('3', plain,
% 0.77/1.01      (((r2_hidden @ sk_A @ sk_B)
% 0.77/1.01        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('4', plain,
% 0.77/1.01      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('split', [status(esa)], ['3'])).
% 0.77/1.01  thf(l31_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( r2_hidden @ A @ B ) =>
% 0.77/1.01       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.77/1.01  thf('5', plain,
% 0.77/1.01      (![X50 : $i, X51 : $i]:
% 0.77/1.01         (((k3_xboole_0 @ X51 @ (k1_tarski @ X50)) = (k1_tarski @ X50))
% 0.77/1.01          | ~ (r2_hidden @ X50 @ X51))),
% 0.77/1.01      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.77/1.01  thf('6', plain,
% 0.77/1.01      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/1.01  thf(t100_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.77/1.01  thf('7', plain,
% 0.77/1.01      (![X4 : $i, X5 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X4 @ X5)
% 0.77/1.01           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('8', plain,
% 0.77/1.01      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf(t93_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k2_xboole_0 @ A @ B ) =
% 0.77/1.01       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.77/1.01  thf('9', plain,
% 0.77/1.01      (![X14 : $i, X15 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X14 @ X15)
% 0.77/1.01           = (k2_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.77/1.01              (k3_xboole_0 @ X14 @ X15)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.77/1.01  thf('10', plain,
% 0.77/1.01      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.77/1.01             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['8', '9'])).
% 0.77/1.01  thf('11', plain,
% 0.77/1.01      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/1.01  thf('12', plain,
% 0.77/1.01      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.77/1.01             (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['10', '11'])).
% 0.77/1.01  thf(t6_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/1.01  thf('13', plain,
% 0.77/1.01      (![X8 : $i, X9 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9))
% 0.77/1.01           = (k2_xboole_0 @ X8 @ X9))),
% 0.77/1.01      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.77/1.01  thf('14', plain,
% 0.77/1.01      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.77/1.01          (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/1.01          = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.77/1.01             (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['12', '13'])).
% 0.77/1.01  thf('15', plain,
% 0.77/1.01      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.77/1.01             (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['10', '11'])).
% 0.77/1.01  thf('16', plain,
% 0.77/1.01      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.77/1.01          (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/1.01          = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['14', '15'])).
% 0.77/1.01  thf(t92_xboole_1, axiom,
% 0.77/1.01    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.77/1.01  thf('17', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/1.01  thf('18', plain,
% 0.77/1.01      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf(t95_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k3_xboole_0 @ A @ B ) =
% 0.77/1.01       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.77/1.01  thf('19', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X16 @ X17)
% 0.77/1.01           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.77/1.01              (k2_xboole_0 @ X16 @ X17)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.77/1.01  thf(commutativity_k5_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.77/1.01  thf('20', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('21', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X16 @ X17)
% 0.77/1.01           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.77/1.01              (k5_xboole_0 @ X16 @ X17)))),
% 0.77/1.01      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/1.01  thf('22', plain,
% 0.77/1.01      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.77/1.01             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['18', '21'])).
% 0.77/1.01  thf('23', plain,
% 0.77/1.01      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/1.01  thf('24', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('25', plain,
% 0.77/1.01      ((((k1_tarski @ sk_A)
% 0.77/1.01          = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.77/1.01             (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.77/1.01  thf('26', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/1.01  thf('27', plain,
% 0.77/1.01      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf(t91_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.77/1.01       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.77/1.01  thf('28', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.77/1.01           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/1.01  thf('29', plain,
% 0.77/1.01      ((![X0 : $i]:
% 0.77/1.01          ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.77/1.01            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['27', '28'])).
% 0.77/1.01  thf('30', plain,
% 0.77/1.01      ((((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.77/1.01          (k1_tarski @ sk_A)) = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['26', '29'])).
% 0.77/1.01  thf('31', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('32', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('33', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf(t5_boole, axiom,
% 0.77/1.01    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.77/1.01  thf('34', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.77/1.01      inference('cnf', [status(esa)], [t5_boole])).
% 0.77/1.01  thf('35', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['33', '34'])).
% 0.77/1.01  thf('36', plain,
% 0.77/1.01      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['30', '31', '32', '35'])).
% 0.77/1.01  thf('37', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.77/1.01           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/1.01  thf('38', plain,
% 0.77/1.01      ((![X0 : $i]:
% 0.77/1.01          ((k5_xboole_0 @ sk_B @ X0)
% 0.77/1.01            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01               (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['36', '37'])).
% 0.77/1.01  thf('39', plain,
% 0.77/1.01      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/1.01          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['25', '38'])).
% 0.77/1.01  thf('40', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/1.01  thf('41', plain,
% 0.77/1.01      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/1.01          = (k1_xboole_0)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['39', '40'])).
% 0.77/1.01  thf('42', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.77/1.01           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/1.01  thf('43', plain,
% 0.77/1.01      ((![X0 : $i]:
% 0.77/1.01          ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.77/1.01            = (k5_xboole_0 @ sk_B @ 
% 0.77/1.01               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['41', '42'])).
% 0.77/1.01  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['33', '34'])).
% 0.77/1.01  thf('45', plain,
% 0.77/1.01      ((![X0 : $i]:
% 0.77/1.01          ((X0)
% 0.77/1.01            = (k5_xboole_0 @ sk_B @ 
% 0.77/1.01               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['43', '44'])).
% 0.77/1.01  thf('46', plain,
% 0.77/1.01      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['17', '45'])).
% 0.77/1.01  thf('47', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['33', '34'])).
% 0.77/1.01  thf('49', plain,
% 0.77/1.01      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.77/1.01  thf('50', plain,
% 0.77/1.01      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.77/1.01  thf('51', plain,
% 0.77/1.01      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.77/1.01          = (sk_B)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['16', '49', '50'])).
% 0.77/1.01  thf('52', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X16 @ X17)
% 0.77/1.01           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.77/1.01              (k5_xboole_0 @ X16 @ X17)))),
% 0.77/1.01      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/1.01  thf('53', plain,
% 0.77/1.01      ((((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ 
% 0.77/1.01             (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['51', '52'])).
% 0.77/1.01  thf('54', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('55', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/1.01  thf('56', plain,
% 0.77/1.01      ((![X0 : $i]:
% 0.77/1.01          ((k5_xboole_0 @ sk_B @ X0)
% 0.77/1.01            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01               (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['36', '37'])).
% 0.77/1.01  thf('57', plain,
% 0.77/1.01      ((((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/1.01          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['55', '56'])).
% 0.77/1.01  thf('58', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['33', '34'])).
% 0.77/1.01  thf('60', plain,
% 0.77/1.01      ((((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/1.01          = (k1_tarski @ sk_A)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.77/1.01  thf('61', plain,
% 0.77/1.01      ((((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['53', '54', '60'])).
% 0.77/1.01  thf('62', plain,
% 0.77/1.01      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf('63', plain,
% 0.77/1.01      ((((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.77/1.01          = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['61', '62'])).
% 0.77/1.01  thf('64', plain,
% 0.77/1.01      (![X14 : $i, X15 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X14 @ X15)
% 0.77/1.01           = (k2_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.77/1.01              (k3_xboole_0 @ X14 @ X15)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.77/1.01  thf('65', plain,
% 0.77/1.01      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.77/1.01          = (k2_xboole_0 @ 
% 0.77/1.01             (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B) @ 
% 0.77/1.01             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['63', '64'])).
% 0.77/1.01  thf('66', plain,
% 0.77/1.01      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.77/1.01          = (sk_B)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['16', '49', '50'])).
% 0.77/1.01  thf('67', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('68', plain,
% 0.77/1.01      ((((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/1.01          = (k1_tarski @ sk_A)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.77/1.01  thf('69', plain,
% 0.77/1.01      ((((sk_B)
% 0.77/1.01          = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.77/1.01  thf('70', plain,
% 0.77/1.01      (![X8 : $i, X9 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9))
% 0.77/1.01           = (k2_xboole_0 @ X8 @ X9))),
% 0.77/1.01      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.77/1.01  thf('71', plain,
% 0.77/1.01      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.77/1.01          = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['69', '70'])).
% 0.77/1.01  thf('72', plain,
% 0.77/1.01      ((((sk_B)
% 0.77/1.01          = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.77/1.01  thf('73', plain,
% 0.77/1.01      ((((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['71', '72'])).
% 0.77/1.01  thf('74', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X16 @ X17)
% 0.77/1.01           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.77/1.01              (k5_xboole_0 @ X16 @ X17)))),
% 0.77/1.01      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/1.01  thf('75', plain,
% 0.77/1.01      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['73', '74'])).
% 0.77/1.01  thf('76', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('77', plain,
% 0.77/1.01      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf('78', plain,
% 0.77/1.01      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.77/1.01          = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.77/1.01  thf('79', plain,
% 0.77/1.01      ((((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.77/1.01          = (k1_tarski @ sk_A)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.77/1.01  thf('80', plain,
% 0.77/1.01      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['78', '79'])).
% 0.77/1.01  thf('81', plain,
% 0.77/1.01      (![X4 : $i, X5 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X4 @ X5)
% 0.77/1.01           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('82', plain,
% 0.77/1.01      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.77/1.01          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['80', '81'])).
% 0.77/1.01  thf(idempotence_k3_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/1.01  thf('83', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.77/1.01      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.77/1.01  thf('84', plain,
% 0.77/1.01      (![X4 : $i, X5 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X4 @ X5)
% 0.77/1.01           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('85', plain,
% 0.77/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['83', '84'])).
% 0.77/1.01  thf('86', plain,
% 0.77/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['83', '84'])).
% 0.77/1.01  thf('87', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/1.01  thf('88', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['86', '87'])).
% 0.77/1.01  thf('89', plain,
% 0.77/1.01      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.77/1.01         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['82', '85', '88'])).
% 0.77/1.01  thf('90', plain,
% 0.77/1.01      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.77/1.01         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.77/1.01      inference('split', [status(esa)], ['0'])).
% 0.77/1.01  thf('91', plain,
% 0.77/1.01      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.77/1.01         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.77/1.01             ((r2_hidden @ sk_A @ sk_B)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['89', '90'])).
% 0.77/1.01  thf('92', plain,
% 0.77/1.01      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.77/1.01       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.77/1.01      inference('simplify', [status(thm)], ['91'])).
% 0.77/1.01  thf('93', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.77/1.01      inference('sat_resolution*', [status(thm)], ['2', '92'])).
% 0.77/1.01  thf('94', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.77/1.01      inference('simpl_trail', [status(thm)], ['1', '93'])).
% 0.77/1.01  thf('95', plain,
% 0.77/1.01      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.77/1.01         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.77/1.01      inference('split', [status(esa)], ['3'])).
% 0.77/1.01  thf('96', plain,
% 0.77/1.01      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.77/1.01       ((r2_hidden @ sk_A @ sk_B))),
% 0.77/1.01      inference('split', [status(esa)], ['3'])).
% 0.77/1.01  thf('97', plain,
% 0.77/1.01      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.77/1.01      inference('sat_resolution*', [status(thm)], ['2', '92', '96'])).
% 0.77/1.01  thf('98', plain,
% 0.77/1.01      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.77/1.01      inference('simpl_trail', [status(thm)], ['95', '97'])).
% 0.77/1.01  thf('99', plain,
% 0.77/1.01      (![X4 : $i, X5 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X4 @ X5)
% 0.77/1.01           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('100', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/1.01  thf('101', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.77/1.01           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/1.01  thf('102', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.77/1.01           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['100', '101'])).
% 0.77/1.01  thf('103', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['33', '34'])).
% 0.77/1.01  thf('104', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['102', '103'])).
% 0.77/1.01  thf('105', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X1 @ X0)
% 0.77/1.01           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['99', '104'])).
% 0.77/1.01  thf('106', plain,
% 0.77/1.01      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.77/1.01         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['98', '105'])).
% 0.77/1.01  thf('107', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('108', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['33', '34'])).
% 0.77/1.01  thf('109', plain,
% 0.77/1.01      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.77/1.01      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.77/1.01  thf('110', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X16 @ X17)
% 0.77/1.01           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.77/1.01              (k5_xboole_0 @ X16 @ X17)))),
% 0.77/1.01      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/1.01  thf('111', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['102', '103'])).
% 0.77/1.01  thf('112', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ X1 @ X0)
% 0.77/1.01           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['110', '111'])).
% 0.77/1.01  thf('113', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('114', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ X1 @ X0)
% 0.77/1.01           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['112', '113'])).
% 0.77/1.01  thf('115', plain,
% 0.77/1.01      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.77/1.01         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01            (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['109', '114'])).
% 0.77/1.01  thf('116', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf(commutativity_k2_tarski, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.77/1.01  thf('117', plain,
% 0.77/1.01      (![X18 : $i, X19 : $i]:
% 0.77/1.01         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.77/1.01  thf(l51_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/1.01  thf('118', plain,
% 0.77/1.01      (![X52 : $i, X53 : $i]:
% 0.77/1.01         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.77/1.01      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/1.01  thf('119', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('sup+', [status(thm)], ['117', '118'])).
% 0.77/1.01  thf('120', plain,
% 0.77/1.01      (![X52 : $i, X53 : $i]:
% 0.77/1.01         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 0.77/1.01      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.77/1.01  thf('121', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('sup+', [status(thm)], ['119', '120'])).
% 0.77/1.01  thf('122', plain,
% 0.77/1.01      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01            (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('demod', [status(thm)], ['115', '116', '121'])).
% 0.77/1.01  thf('123', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['102', '103'])).
% 0.77/1.01  thf('124', plain,
% 0.77/1.01      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['122', '123'])).
% 0.77/1.01  thf('125', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('126', plain,
% 0.77/1.01      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.77/1.01      inference('simpl_trail', [status(thm)], ['95', '97'])).
% 0.77/1.01  thf('127', plain,
% 0.77/1.01      (![X4 : $i, X5 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X4 @ X5)
% 0.77/1.01           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('128', plain,
% 0.77/1.01      (![X14 : $i, X15 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X14 @ X15)
% 0.77/1.01           = (k2_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.77/1.01              (k3_xboole_0 @ X14 @ X15)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.77/1.01  thf('129', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/1.01           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.77/1.01              (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['127', '128'])).
% 0.77/1.01  thf('130', plain,
% 0.77/1.01      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.77/1.01         = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['126', '129'])).
% 0.77/1.01  thf('131', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/1.01  thf('132', plain,
% 0.77/1.01      (![X14 : $i, X15 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X14 @ X15)
% 0.77/1.01           = (k2_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.77/1.01              (k3_xboole_0 @ X14 @ X15)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.77/1.01  thf('133', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X0 @ X0)
% 0.77/1.01           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['131', '132'])).
% 0.77/1.01  thf(idempotence_k2_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/1.01  thf('134', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/1.01      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.77/1.01  thf('135', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.77/1.01      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.77/1.01  thf('136', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.77/1.01      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.77/1.01  thf('137', plain,
% 0.77/1.01      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.77/1.01         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['130', '136'])).
% 0.77/1.01  thf('138', plain,
% 0.77/1.01      (![X8 : $i, X9 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9))
% 0.77/1.01           = (k2_xboole_0 @ X8 @ X9))),
% 0.77/1.01      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.77/1.01  thf('139', plain,
% 0.77/1.01      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01          (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.77/1.01         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['137', '138'])).
% 0.77/1.01  thf('140', plain,
% 0.77/1.01      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.77/1.01         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['130', '136'])).
% 0.77/1.01  thf('141', plain,
% 0.77/1.01      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01          (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.77/1.01         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['139', '140'])).
% 0.77/1.01  thf('142', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X16 @ X17)
% 0.77/1.01           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.77/1.01              (k5_xboole_0 @ X16 @ X17)))),
% 0.77/1.01      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/1.01  thf('143', plain,
% 0.77/1.01      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01          (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.77/1.01         = (k5_xboole_0 @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 0.77/1.01            (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01              (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['141', '142'])).
% 0.77/1.01  thf('144', plain,
% 0.77/1.01      (![X4 : $i, X5 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X4 @ X5)
% 0.77/1.01           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('145', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('146', plain,
% 0.77/1.01      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01          (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.77/1.01         = (k5_xboole_0 @ 
% 0.77/1.01            (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.77/1.01      inference('demod', [status(thm)], ['143', '144', '145'])).
% 0.77/1.01  thf('147', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.77/1.01           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/1.01  thf('148', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ 
% 0.77/1.01           (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))) @ 
% 0.77/1.01           X0)
% 0.77/1.01           = (k5_xboole_0 @ 
% 0.77/1.01              (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01               (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 0.77/1.01              (k5_xboole_0 @ 
% 0.77/1.01               (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01                (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 0.77/1.01               X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['146', '147'])).
% 0.77/1.01  thf('149', plain,
% 0.77/1.01      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.77/1.01         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/1.01      inference('demod', [status(thm)], ['130', '136'])).
% 0.77/1.01  thf('150', plain,
% 0.77/1.01      (![X8 : $i, X9 : $i]:
% 0.77/1.01         ((k2_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9))
% 0.77/1.01           = (k2_xboole_0 @ X8 @ X9))),
% 0.77/1.01      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.77/1.01  thf('151', plain,
% 0.77/1.01      (![X16 : $i, X17 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X16 @ X17)
% 0.77/1.01           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.77/1.01              (k5_xboole_0 @ X16 @ X17)))),
% 0.77/1.01      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/1.01  thf('152', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.77/1.01           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.77/1.01              (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['150', '151'])).
% 0.77/1.01  thf('153', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('154', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['102', '103'])).
% 0.77/1.01  thf('155', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['153', '154'])).
% 0.77/1.01  thf('156', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.77/1.01      inference('demod', [status(thm)], ['152', '155'])).
% 0.77/1.01  thf('157', plain,
% 0.77/1.01      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01          (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.77/1.01         = (k1_tarski @ sk_A))),
% 0.77/1.01      inference('sup+', [status(thm)], ['149', '156'])).
% 0.77/1.01  thf('158', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.77/1.01           = (k5_xboole_0 @ 
% 0.77/1.01              (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01               (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 0.77/1.01              (k5_xboole_0 @ 
% 0.77/1.01               (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01                (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 0.77/1.01               X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['148', '157'])).
% 0.77/1.01  thf('159', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.77/1.01           = (k5_xboole_0 @ 
% 0.77/1.01              (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01               (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 0.77/1.01              (k5_xboole_0 @ X0 @ 
% 0.77/1.01               (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01                (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['125', '158'])).
% 0.77/1.01  thf('160', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.77/1.01           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/1.01  thf('161', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('162', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.77/1.01           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['160', '161'])).
% 0.77/1.01  thf('163', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ 
% 0.77/1.01           (k5_xboole_0 @ X0 @ 
% 0.77/1.01            (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))) @ 
% 0.77/1.01           (k5_xboole_0 @ X1 @ 
% 0.77/1.01            (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01             (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 0.77/1.01           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['159', '162'])).
% 0.77/1.01  thf('164', plain,
% 0.77/1.01      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.77/1.01           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/1.01  thf('165', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.77/1.01           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['160', '161'])).
% 0.77/1.01  thf('166', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.77/1.01           = (k5_xboole_0 @ 
% 0.77/1.01              (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01               (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 0.77/1.01              (k5_xboole_0 @ 
% 0.77/1.01               (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.77/1.01                (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) @ 
% 0.77/1.01               X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['148', '157'])).
% 0.77/1.01  thf('167', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X1))
% 0.77/1.01           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 0.77/1.01  thf('168', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.77/1.01           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['160', '161'])).
% 0.77/1.01  thf('169', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.77/1.01           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['167', '168'])).
% 0.77/1.01  thf('170', plain,
% 0.77/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['83', '84'])).
% 0.77/1.01  thf('171', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['86', '87'])).
% 0.77/1.01  thf('172', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('173', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['33', '34'])).
% 0.77/1.01  thf('174', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.77/1.01      inference('demod', [status(thm)],
% 0.77/1.01                ['124', '169', '170', '171', '172', '173'])).
% 0.77/1.01  thf('175', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k5_xboole_0 @ X1 @ X0)
% 0.77/1.01           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['112', '113'])).
% 0.77/1.01  thf('176', plain,
% 0.77/1.01      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.77/1.01      inference('sup+', [status(thm)], ['174', '175'])).
% 0.77/1.01  thf('177', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.77/1.01  thf('178', plain,
% 0.77/1.01      (![X4 : $i, X5 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X4 @ X5)
% 0.77/1.01           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('179', plain,
% 0.77/1.01      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/1.01         = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('demod', [status(thm)], ['176', '177', '178'])).
% 0.77/1.01  thf('180', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('demod', [status(thm)], ['102', '103'])).
% 0.77/1.01  thf('181', plain,
% 0.77/1.01      (((k1_tarski @ sk_A)
% 0.77/1.01         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['179', '180'])).
% 0.77/1.01  thf('182', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X1 @ X0)
% 0.77/1.01           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['99', '104'])).
% 0.77/1.01  thf('183', plain,
% 0.77/1.01      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.77/1.01      inference('demod', [status(thm)], ['181', '182'])).
% 0.77/1.01  thf(l29_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.77/1.01       ( r2_hidden @ B @ A ) ))).
% 0.77/1.01  thf('184', plain,
% 0.77/1.01      (![X48 : $i, X49 : $i]:
% 0.77/1.01         ((r2_hidden @ X48 @ X49)
% 0.77/1.01          | ((k3_xboole_0 @ X49 @ (k1_tarski @ X48)) != (k1_tarski @ X48)))),
% 0.77/1.01      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.77/1.01  thf('185', plain,
% 0.77/1.01      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.77/1.01      inference('sup-', [status(thm)], ['183', '184'])).
% 0.77/1.01  thf('186', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.77/1.01      inference('simplify', [status(thm)], ['185'])).
% 0.77/1.01  thf('187', plain, ($false), inference('demod', [status(thm)], ['94', '186'])).
% 0.77/1.01  
% 0.77/1.01  % SZS output end Refutation
% 0.77/1.01  
% 0.86/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
