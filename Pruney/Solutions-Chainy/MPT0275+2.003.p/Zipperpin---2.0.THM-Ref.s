%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i3PDj7i4dz

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:36 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 301 expanded)
%              Number of leaves         :   24 ( 105 expanded)
%              Depth                    :   16
%              Number of atoms          :  851 (2573 expanded)
%              Number of equality atoms :   83 ( 287 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t73_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = k1_xboole_0 )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('27',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
      = sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('29',plain,
    ( ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,
    ( ( ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('33',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('39',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_hidden @ X48 @ X47 )
      | ~ ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['42'])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X49 )
      | ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r2_hidden @ X46 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('52',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,
    ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('56',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C @ sk_C ) ) )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('60',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('69',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('70',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ~ ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('71',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['42'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','44','45','67','68','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i3PDj7i4dz
% 0.15/0.38  % Computer   : n001.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 16:24:00 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 558 iterations in 0.257s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(t73_zfmisc_1, conjecture,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.70       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.71        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.71          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t73_zfmisc_1])).
% 0.54/0.71  thf('0', plain,
% 0.54/0.71      (((r2_hidden @ sk_B @ sk_C)
% 0.54/0.71        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('1', plain,
% 0.54/0.71      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.71       ((r2_hidden @ sk_B @ sk_C))),
% 0.54/0.71      inference('split', [status(esa)], ['0'])).
% 0.54/0.71  thf('2', plain,
% 0.54/0.71      (((r2_hidden @ sk_A @ sk_C)
% 0.54/0.71        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('3', plain,
% 0.54/0.71      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('split', [status(esa)], ['2'])).
% 0.54/0.71  thf(t95_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k3_xboole_0 @ A @ B ) =
% 0.54/0.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.54/0.71  thf('4', plain,
% 0.54/0.71      (![X13 : $i, X14 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X13 @ X14)
% 0.54/0.71           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 0.54/0.71              (k2_xboole_0 @ X13 @ X14)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.54/0.71  thf(t91_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.54/0.71  thf('5', plain,
% 0.54/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.54/0.71           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.71  thf('6', plain,
% 0.54/0.71      (![X13 : $i, X14 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X13 @ X14)
% 0.54/0.71           = (k5_xboole_0 @ X13 @ 
% 0.54/0.71              (k5_xboole_0 @ X14 @ (k2_xboole_0 @ X13 @ X14))))),
% 0.54/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.54/0.71  thf(t92_xboole_1, axiom,
% 0.54/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.71  thf('7', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.71  thf('8', plain,
% 0.54/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.54/0.71           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.71  thf('9', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['7', '8'])).
% 0.54/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.54/0.71  thf('10', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.71  thf(t5_boole, axiom,
% 0.54/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.71  thf('11', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.54/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.71  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.71  thf('13', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['6', '13'])).
% 0.54/0.71  thf(t100_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      (![X2 : $i, X3 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X2 @ X3)
% 0.54/0.71           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.54/0.71           = (k4_xboole_0 @ X1 @ X0))),
% 0.54/0.71      inference('demod', [status(thm)], ['14', '15'])).
% 0.54/0.71  thf('17', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.71  thf('18', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k2_xboole_0 @ X1 @ X0)
% 0.54/0.71           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.54/0.71  thf('19', plain,
% 0.54/0.71      ((((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.71          = (k5_xboole_0 @ sk_C @ k1_xboole_0)))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup+', [status(thm)], ['3', '18'])).
% 0.54/0.71  thf(commutativity_k2_tarski, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.54/0.71  thf('20', plain,
% 0.54/0.71      (![X15 : $i, X16 : $i]:
% 0.54/0.71         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.54/0.71  thf(l51_zfmisc_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.54/0.71  thf('21', plain,
% 0.54/0.71      (![X44 : $i, X45 : $i]:
% 0.54/0.71         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.54/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.54/0.71  thf('22', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['20', '21'])).
% 0.54/0.71  thf('23', plain,
% 0.54/0.71      (![X44 : $i, X45 : $i]:
% 0.54/0.71         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.54/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.54/0.71  thf('24', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['22', '23'])).
% 0.54/0.71  thf('25', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.71  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.71  thf('27', plain,
% 0.54/0.71      ((((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (sk_C)))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('demod', [status(thm)], ['19', '24', '25', '26'])).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.54/0.71           = (k4_xboole_0 @ X1 @ X0))),
% 0.54/0.71      inference('demod', [status(thm)], ['14', '15'])).
% 0.54/0.71  thf('29', plain,
% 0.54/0.71      ((((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.71          = (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup+', [status(thm)], ['27', '28'])).
% 0.54/0.71  thf('30', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.71  thf('31', plain,
% 0.54/0.71      ((((k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.71          = (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.71  thf('32', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.71  thf('33', plain,
% 0.54/0.71      ((((k2_tarski @ sk_A @ sk_B)
% 0.54/0.71          = (k5_xboole_0 @ sk_C @ 
% 0.54/0.71             (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup+', [status(thm)], ['31', '32'])).
% 0.54/0.71  thf('34', plain,
% 0.54/0.71      (![X2 : $i, X3 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X2 @ X3)
% 0.54/0.71           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.71  thf('35', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.71  thf('36', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X1 @ X0)
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.54/0.71  thf('37', plain,
% 0.54/0.71      ((((k2_tarski @ sk_A @ sk_B)
% 0.54/0.71          = (k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('demod', [status(thm)], ['33', '36'])).
% 0.54/0.71  thf(t17_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.71  thf('38', plain,
% 0.54/0.71      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.54/0.71      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.54/0.71  thf('39', plain,
% 0.54/0.71      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup+', [status(thm)], ['37', '38'])).
% 0.54/0.71  thf(t38_zfmisc_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.54/0.71       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.54/0.71  thf('40', plain,
% 0.54/0.71      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.54/0.71         ((r2_hidden @ X48 @ X47)
% 0.54/0.71          | ~ (r1_tarski @ (k2_tarski @ X46 @ X48) @ X47))),
% 0.54/0.71      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.54/0.71  thf('41', plain,
% 0.54/0.71      (((r2_hidden @ sk_B @ sk_C))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.54/0.71  thf('42', plain,
% 0.54/0.71      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.54/0.71        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.54/0.71        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf('43', plain,
% 0.54/0.71      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('split', [status(esa)], ['42'])).
% 0.54/0.71  thf('44', plain,
% 0.54/0.71      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.71       ((r2_hidden @ sk_B @ sk_C))),
% 0.54/0.71      inference('sup-', [status(thm)], ['41', '43'])).
% 0.54/0.71  thf('45', plain,
% 0.54/0.71      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.54/0.71       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.71       ~ ((r2_hidden @ sk_B @ sk_C))),
% 0.54/0.71      inference('split', [status(esa)], ['42'])).
% 0.54/0.71  thf('46', plain,
% 0.54/0.71      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('split', [status(esa)], ['0'])).
% 0.54/0.71  thf('47', plain,
% 0.54/0.71      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.54/0.71      inference('split', [status(esa)], ['2'])).
% 0.54/0.71  thf('48', plain,
% 0.54/0.71      (![X46 : $i, X48 : $i, X49 : $i]:
% 0.54/0.71         ((r1_tarski @ (k2_tarski @ X46 @ X48) @ X49)
% 0.54/0.71          | ~ (r2_hidden @ X48 @ X49)
% 0.54/0.71          | ~ (r2_hidden @ X46 @ X49))),
% 0.54/0.71      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.54/0.71  thf('49', plain,
% 0.54/0.71      ((![X0 : $i]:
% 0.54/0.71          (~ (r2_hidden @ X0 @ sk_C)
% 0.54/0.71           | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C)))
% 0.54/0.71         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.71  thf('50', plain,
% 0.54/0.71      (((r1_tarski @ (k2_tarski @ sk_B @ sk_A) @ sk_C))
% 0.54/0.71         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['46', '49'])).
% 0.54/0.71  thf('51', plain,
% 0.54/0.71      (![X15 : $i, X16 : $i]:
% 0.54/0.71         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.54/0.71  thf('52', plain,
% 0.54/0.71      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.54/0.71         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('demod', [status(thm)], ['50', '51'])).
% 0.54/0.71  thf(t12_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.54/0.71  thf('53', plain,
% 0.54/0.71      (![X4 : $i, X5 : $i]:
% 0.54/0.71         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.54/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.71  thf('54', plain,
% 0.54/0.71      ((((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (sk_C)))
% 0.54/0.71         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['52', '53'])).
% 0.54/0.71  thf('55', plain,
% 0.54/0.71      (![X13 : $i, X14 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X13 @ X14)
% 0.54/0.71           = (k5_xboole_0 @ X13 @ 
% 0.54/0.71              (k5_xboole_0 @ X14 @ (k2_xboole_0 @ X13 @ X14))))),
% 0.54/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.54/0.71  thf('56', plain,
% 0.54/0.71      ((((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.71          = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.54/0.71             (k5_xboole_0 @ sk_C @ sk_C))))
% 0.54/0.71         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['54', '55'])).
% 0.54/0.71  thf('57', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.71  thf('58', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.71  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.71  thf('60', plain,
% 0.54/0.71      ((((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.71          = (k2_tarski @ sk_A @ sk_B)))
% 0.54/0.71         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.54/0.71  thf('61', plain,
% 0.54/0.71      (![X2 : $i, X3 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X2 @ X3)
% 0.54/0.71           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.71  thf('62', plain,
% 0.54/0.71      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.54/0.71          = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.54/0.71             (k2_tarski @ sk_A @ sk_B))))
% 0.54/0.71         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['60', '61'])).
% 0.54/0.71  thf('63', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.71  thf('64', plain,
% 0.54/0.71      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 0.54/0.71         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('demod', [status(thm)], ['62', '63'])).
% 0.54/0.71  thf('65', plain,
% 0.54/0.71      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))
% 0.54/0.71         <= (~
% 0.54/0.71             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('split', [status(esa)], ['42'])).
% 0.54/0.71  thf('66', plain,
% 0.54/0.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.54/0.71         <= (~
% 0.54/0.71             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) & 
% 0.54/0.71             ((r2_hidden @ sk_A @ sk_C)) & 
% 0.54/0.71             ((r2_hidden @ sk_B @ sk_C)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['64', '65'])).
% 0.54/0.71  thf('67', plain,
% 0.54/0.71      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.71       ~ ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_C))),
% 0.54/0.71      inference('simplify', [status(thm)], ['66'])).
% 0.54/0.71  thf('68', plain,
% 0.54/0.71      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.71       ((r2_hidden @ sk_A @ sk_C))),
% 0.54/0.71      inference('split', [status(esa)], ['2'])).
% 0.54/0.71  thf('69', plain,
% 0.54/0.71      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup+', [status(thm)], ['37', '38'])).
% 0.54/0.71  thf('70', plain,
% 0.54/0.71      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.54/0.71         ((r2_hidden @ X46 @ X47)
% 0.54/0.71          | ~ (r1_tarski @ (k2_tarski @ X46 @ X48) @ X47))),
% 0.54/0.71      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.54/0.71  thf('71', plain,
% 0.54/0.71      (((r2_hidden @ sk_A @ sk_C))
% 0.54/0.71         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 0.54/0.71      inference('sup-', [status(thm)], ['69', '70'])).
% 0.54/0.71  thf('72', plain,
% 0.54/0.71      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.54/0.71      inference('split', [status(esa)], ['42'])).
% 0.54/0.71  thf('73', plain,
% 0.54/0.71      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 0.54/0.71       ((r2_hidden @ sk_A @ sk_C))),
% 0.54/0.71      inference('sup-', [status(thm)], ['71', '72'])).
% 0.54/0.71  thf('74', plain, ($false),
% 0.54/0.71      inference('sat_resolution*', [status(thm)],
% 0.54/0.71                ['1', '44', '45', '67', '68', '73'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
