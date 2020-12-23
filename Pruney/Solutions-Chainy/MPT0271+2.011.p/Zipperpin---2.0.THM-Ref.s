%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O8N9jOXXJa

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:22 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 288 expanded)
%              Number of leaves         :   24 ( 103 expanded)
%              Depth                    :   25
%              Number of atoms          :  996 (2312 expanded)
%              Number of equality atoms :  105 ( 259 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X46: $i,X48: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X46 ) @ X48 )
      | ~ ( r2_hidden @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('7',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22','23','26','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','31','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','51'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X17 @ X16 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
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
    inference('sup+',[status(thm)],['24','25'])).

thf('60',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['52','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('71',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['66','69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('76',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['60','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('82',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['82','90'])).

thf('92',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('99',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ~ ( r1_tarski @ ( k1_tarski @ X46 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('101',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['33','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O8N9jOXXJa
% 0.15/0.36  % Computer   : n021.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:08:49 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.91/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.17  % Solved by: fo/fo7.sh
% 0.91/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.17  % done 1485 iterations in 0.695s
% 0.91/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.17  % SZS output start Refutation
% 0.91/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.17  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.91/1.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.17  thf(t68_zfmisc_1, conjecture,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.17       ( r2_hidden @ A @ B ) ))).
% 0.91/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.17    (~( ![A:$i,B:$i]:
% 0.91/1.17        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.17          ( r2_hidden @ A @ B ) ) )),
% 0.91/1.17    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.91/1.17  thf('0', plain,
% 0.91/1.17      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.91/1.17        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('1', plain,
% 0.91/1.17      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('split', [status(esa)], ['0'])).
% 0.91/1.17  thf('2', plain,
% 0.91/1.17      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.91/1.17       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.17      inference('split', [status(esa)], ['0'])).
% 0.91/1.17  thf(t92_xboole_1, axiom,
% 0.91/1.17    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.91/1.17  thf('3', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.91/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.17  thf('4', plain,
% 0.91/1.17      (((r2_hidden @ sk_A @ sk_B)
% 0.91/1.17        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.17  thf('5', plain,
% 0.91/1.17      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('split', [status(esa)], ['4'])).
% 0.91/1.17  thf(l1_zfmisc_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.91/1.17  thf('6', plain,
% 0.91/1.17      (![X46 : $i, X48 : $i]:
% 0.91/1.17         ((r1_tarski @ (k1_tarski @ X46) @ X48) | ~ (r2_hidden @ X46 @ X48))),
% 0.91/1.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.17  thf('7', plain,
% 0.91/1.17      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.91/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['5', '6'])).
% 0.91/1.17  thf(t12_xboole_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.17  thf('8', plain,
% 0.91/1.17      (![X5 : $i, X6 : $i]:
% 0.91/1.17         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.91/1.17      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.17  thf('9', plain,
% 0.91/1.17      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 0.91/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.17  thf(t95_xboole_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( k3_xboole_0 @ A @ B ) =
% 0.91/1.17       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.91/1.17  thf('10', plain,
% 0.91/1.17      (![X14 : $i, X15 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ X14 @ X15)
% 0.91/1.17           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 0.91/1.17              (k2_xboole_0 @ X14 @ X15)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.91/1.17  thf(commutativity_k5_xboole_0, axiom,
% 0.91/1.17    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.91/1.17  thf('11', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('12', plain,
% 0.91/1.17      (![X14 : $i, X15 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ X14 @ X15)
% 0.91/1.17           = (k5_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ 
% 0.91/1.17              (k5_xboole_0 @ X14 @ X15)))),
% 0.91/1.17      inference('demod', [status(thm)], ['10', '11'])).
% 0.91/1.17  thf('13', plain,
% 0.91/1.17      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.17          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 0.91/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['9', '12'])).
% 0.91/1.17  thf('14', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('15', plain,
% 0.91/1.17      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.17          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.91/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('demod', [status(thm)], ['13', '14'])).
% 0.91/1.17  thf(t91_xboole_1, axiom,
% 0.91/1.17    (![A:$i,B:$i,C:$i]:
% 0.91/1.17     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.17       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.91/1.17  thf('16', plain,
% 0.91/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.91/1.17           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.17  thf('17', plain,
% 0.91/1.17      ((![X0 : $i]:
% 0.91/1.17          ((k5_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)
% 0.91/1.17            = (k5_xboole_0 @ sk_B @ 
% 0.91/1.17               (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.91/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['15', '16'])).
% 0.91/1.17  thf('18', plain,
% 0.91/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.91/1.17           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.17  thf('19', plain,
% 0.91/1.17      ((![X0 : $i]:
% 0.91/1.17          ((k5_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)
% 0.91/1.17            = (k5_xboole_0 @ sk_B @ 
% 0.91/1.17               (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))))
% 0.91/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('demod', [status(thm)], ['17', '18'])).
% 0.91/1.17  thf('20', plain,
% 0.91/1.17      ((((k5_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.91/1.17          (k1_tarski @ sk_A))
% 0.91/1.17          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ k1_xboole_0))))
% 0.91/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['3', '19'])).
% 0.91/1.17  thf('21', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf(t100_xboole_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.17  thf('22', plain,
% 0.91/1.17      (![X3 : $i, X4 : $i]:
% 0.91/1.17         ((k4_xboole_0 @ X3 @ X4)
% 0.91/1.17           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.17  thf('23', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('24', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf(t5_boole, axiom,
% 0.91/1.17    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.17  thf('25', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.91/1.17      inference('cnf', [status(esa)], [t5_boole])).
% 0.91/1.17  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.17      inference('sup+', [status(thm)], ['24', '25'])).
% 0.91/1.17  thf('27', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.91/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.17  thf('28', plain,
% 0.91/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.91/1.17         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('demod', [status(thm)], ['20', '21', '22', '23', '26', '27'])).
% 0.91/1.17  thf('29', plain,
% 0.91/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.91/1.17         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.17      inference('split', [status(esa)], ['0'])).
% 0.91/1.17  thf('30', plain,
% 0.91/1.17      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.91/1.17         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.91/1.17             ((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.17      inference('sup-', [status(thm)], ['28', '29'])).
% 0.91/1.17  thf('31', plain,
% 0.91/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.91/1.17       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.17      inference('simplify', [status(thm)], ['30'])).
% 0.91/1.17  thf('32', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.17      inference('sat_resolution*', [status(thm)], ['2', '31'])).
% 0.91/1.17  thf('33', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.91/1.17      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.91/1.17  thf('34', plain,
% 0.91/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.91/1.17         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.17      inference('split', [status(esa)], ['4'])).
% 0.91/1.17  thf('35', plain,
% 0.91/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.91/1.17       ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.17      inference('split', [status(esa)], ['4'])).
% 0.91/1.17  thf('36', plain,
% 0.91/1.17      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.17      inference('sat_resolution*', [status(thm)], ['2', '31', '35'])).
% 0.91/1.17  thf('37', plain,
% 0.91/1.17      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.91/1.17      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 0.91/1.17  thf('38', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('39', plain,
% 0.91/1.17      (![X14 : $i, X15 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ X14 @ X15)
% 0.91/1.17           = (k5_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ 
% 0.91/1.17              (k5_xboole_0 @ X14 @ X15)))),
% 0.91/1.17      inference('demod', [status(thm)], ['10', '11'])).
% 0.91/1.17  thf('40', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ X0 @ X1)
% 0.91/1.17           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['38', '39'])).
% 0.91/1.17  thf('41', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('42', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.91/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.17  thf('43', plain,
% 0.91/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.91/1.17           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.17  thf('44', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.91/1.17           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['42', '43'])).
% 0.91/1.17  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.17      inference('sup+', [status(thm)], ['24', '25'])).
% 0.91/1.17  thf('46', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('demod', [status(thm)], ['44', '45'])).
% 0.91/1.17  thf('47', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['41', '46'])).
% 0.91/1.17  thf('48', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k2_xboole_0 @ X1 @ X0)
% 0.91/1.17           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['40', '47'])).
% 0.91/1.17  thf('49', plain,
% 0.91/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.91/1.17           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.17  thf('50', plain,
% 0.91/1.17      (![X3 : $i, X4 : $i]:
% 0.91/1.17         ((k4_xboole_0 @ X3 @ X4)
% 0.91/1.17           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.17  thf('51', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k2_xboole_0 @ X1 @ X0)
% 0.91/1.17           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.91/1.17  thf('52', plain,
% 0.91/1.17      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.17         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.91/1.17      inference('sup+', [status(thm)], ['37', '51'])).
% 0.91/1.17  thf(commutativity_k2_tarski, axiom,
% 0.91/1.17    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.91/1.17  thf('53', plain,
% 0.91/1.17      (![X16 : $i, X17 : $i]:
% 0.91/1.17         ((k2_tarski @ X17 @ X16) = (k2_tarski @ X16 @ X17))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.91/1.17  thf(l51_zfmisc_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]:
% 0.91/1.17     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.17  thf('54', plain,
% 0.91/1.17      (![X49 : $i, X50 : $i]:
% 0.91/1.17         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.91/1.17      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.17  thf('55', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('sup+', [status(thm)], ['53', '54'])).
% 0.91/1.17  thf('56', plain,
% 0.91/1.17      (![X49 : $i, X50 : $i]:
% 0.91/1.17         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.91/1.17      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.17  thf('57', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('sup+', [status(thm)], ['55', '56'])).
% 0.91/1.17  thf('58', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.17      inference('sup+', [status(thm)], ['24', '25'])).
% 0.91/1.17  thf('60', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.91/1.17      inference('demod', [status(thm)], ['52', '57', '58', '59'])).
% 0.91/1.17  thf('61', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('demod', [status(thm)], ['44', '45'])).
% 0.91/1.17  thf('62', plain,
% 0.91/1.17      (![X14 : $i, X15 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ X14 @ X15)
% 0.91/1.17           = (k5_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ 
% 0.91/1.17              (k5_xboole_0 @ X14 @ X15)))),
% 0.91/1.17      inference('demod', [status(thm)], ['10', '11'])).
% 0.91/1.17  thf('63', plain,
% 0.91/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.91/1.17           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.17  thf('64', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.91/1.17           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.91/1.17              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['62', '63'])).
% 0.91/1.17  thf('65', plain,
% 0.91/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.91/1.17           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.17  thf('66', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.91/1.17           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.91/1.17              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 0.91/1.17      inference('demod', [status(thm)], ['64', '65'])).
% 0.91/1.17  thf('67', plain,
% 0.91/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.91/1.17           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.17  thf('68', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('69', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.91/1.17           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['67', '68'])).
% 0.91/1.17  thf('70', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('71', plain,
% 0.91/1.17      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12)
% 0.91/1.17           = (k5_xboole_0 @ X10 @ (k5_xboole_0 @ X11 @ X12)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.17  thf('72', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.91/1.17           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['70', '71'])).
% 0.91/1.17  thf('73', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.91/1.17           = (k5_xboole_0 @ X1 @ 
% 0.91/1.17              (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.91/1.17      inference('demod', [status(thm)], ['66', '69', '72'])).
% 0.91/1.17  thf('74', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.91/1.17           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['61', '73'])).
% 0.91/1.17  thf('75', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('76', plain,
% 0.91/1.17      (![X3 : $i, X4 : $i]:
% 0.91/1.17         ((k4_xboole_0 @ X3 @ X4)
% 0.91/1.17           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.17  thf('77', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k4_xboole_0 @ X1 @ X0)
% 0.91/1.17           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.91/1.17  thf('78', plain,
% 0.91/1.17      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.91/1.17         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.91/1.17      inference('sup+', [status(thm)], ['60', '77'])).
% 0.91/1.17  thf('79', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('80', plain,
% 0.91/1.17      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.91/1.17         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.91/1.17      inference('demod', [status(thm)], ['78', '79'])).
% 0.91/1.17  thf('81', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('demod', [status(thm)], ['44', '45'])).
% 0.91/1.17  thf('82', plain,
% 0.91/1.17      (((k1_tarski @ sk_A)
% 0.91/1.17         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.91/1.17      inference('sup+', [status(thm)], ['80', '81'])).
% 0.91/1.17  thf(t17_xboole_1, axiom,
% 0.91/1.17    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.91/1.17  thf('83', plain,
% 0.91/1.17      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.91/1.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.91/1.17  thf('84', plain,
% 0.91/1.17      (![X5 : $i, X6 : $i]:
% 0.91/1.17         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.91/1.17      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.17  thf('85', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.91/1.17      inference('sup-', [status(thm)], ['83', '84'])).
% 0.91/1.17  thf('86', plain,
% 0.91/1.17      (![X14 : $i, X15 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ X14 @ X15)
% 0.91/1.17           = (k5_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ 
% 0.91/1.17              (k5_xboole_0 @ X14 @ X15)))),
% 0.91/1.17      inference('demod', [status(thm)], ['10', '11'])).
% 0.91/1.17  thf('87', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.91/1.17           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['85', '86'])).
% 0.91/1.17  thf('88', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.17  thf('89', plain,
% 0.91/1.17      (![X3 : $i, X4 : $i]:
% 0.91/1.17         ((k4_xboole_0 @ X3 @ X4)
% 0.91/1.17           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.17  thf('90', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.91/1.17           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.17      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.91/1.17  thf('91', plain,
% 0.91/1.17      (((k1_tarski @ sk_A)
% 0.91/1.17         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B))),
% 0.91/1.17      inference('demod', [status(thm)], ['82', '90'])).
% 0.91/1.17  thf('92', plain,
% 0.91/1.17      (![X3 : $i, X4 : $i]:
% 0.91/1.17         ((k4_xboole_0 @ X3 @ X4)
% 0.91/1.17           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.17  thf('93', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('demod', [status(thm)], ['44', '45'])).
% 0.91/1.17  thf('94', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ X1 @ X0)
% 0.91/1.17           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.91/1.17      inference('sup+', [status(thm)], ['92', '93'])).
% 0.91/1.17  thf('95', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.91/1.17           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.91/1.17      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.91/1.17  thf('96', plain,
% 0.91/1.17      (![X0 : $i, X1 : $i]:
% 0.91/1.17         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.91/1.17           = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.17      inference('sup+', [status(thm)], ['94', '95'])).
% 0.91/1.17  thf('97', plain,
% 0.91/1.17      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.91/1.17      inference('demod', [status(thm)], ['91', '96'])).
% 0.91/1.17  thf('98', plain,
% 0.91/1.17      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.91/1.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.91/1.17  thf('99', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.91/1.17      inference('sup+', [status(thm)], ['97', '98'])).
% 0.91/1.17  thf('100', plain,
% 0.91/1.17      (![X46 : $i, X47 : $i]:
% 0.91/1.17         ((r2_hidden @ X46 @ X47) | ~ (r1_tarski @ (k1_tarski @ X46) @ X47))),
% 0.91/1.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.17  thf('101', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.91/1.17      inference('sup-', [status(thm)], ['99', '100'])).
% 0.91/1.17  thf('102', plain, ($false), inference('demod', [status(thm)], ['33', '101'])).
% 0.91/1.17  
% 0.91/1.17  % SZS output end Refutation
% 0.91/1.17  
% 0.91/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
