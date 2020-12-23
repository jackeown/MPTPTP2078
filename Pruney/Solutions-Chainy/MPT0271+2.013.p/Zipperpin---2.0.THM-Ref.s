%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JTFZb7ztss

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:22 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 723 expanded)
%              Number of leaves         :   28 ( 239 expanded)
%              Depth                    :   29
%              Number of atoms          : 1194 (6169 expanded)
%              Number of equality atoms :  133 ( 687 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t52_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k3_xboole_0 @ X57 @ ( k1_tarski @ X56 ) )
        = ( k1_tarski @ X56 ) )
      | ~ ( r2_hidden @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t52_zfmisc_1])).

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

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

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

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['20','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('50',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('53',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','19','50','55'])).

thf('57',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('58',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','65'])).

thf('67',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','66'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('69',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('70',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','65','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('74',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('75',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','79'])).

thf('81',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('82',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('90',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('91',plain,(
    ! [X55: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X55 ) )
      = X55 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('95',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('97',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X48 ) @ X49 )
      | ( r2_hidden @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('98',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('102',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','111'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('113',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53 != X52 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X52 ) )
       != ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('114',plain,(
    ! [X52: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ ( k1_tarski @ X52 ) )
     != ( k1_tarski @ X52 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('116',plain,(
    ! [X52: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X52 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['112','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','117'])).

thf('119',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['88','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['67','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JTFZb7ztss
% 0.13/0.36  % Computer   : n011.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:03:12 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.62/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.79  % Solved by: fo/fo7.sh
% 0.62/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.79  % done 704 iterations in 0.356s
% 0.62/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.79  % SZS output start Refutation
% 0.62/0.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.62/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.79  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.62/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.62/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.79  thf(t68_zfmisc_1, conjecture,
% 0.62/0.79    (![A:$i,B:$i]:
% 0.62/0.79     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.62/0.79       ( r2_hidden @ A @ B ) ))).
% 0.62/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.79    (~( ![A:$i,B:$i]:
% 0.62/0.79        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.62/0.79          ( r2_hidden @ A @ B ) ) )),
% 0.62/0.79    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.62/0.79  thf('0', plain,
% 0.62/0.79      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.62/0.79        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.62/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.79  thf('1', plain,
% 0.62/0.79      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('split', [status(esa)], ['0'])).
% 0.62/0.79  thf('2', plain,
% 0.62/0.79      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.62/0.79       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.62/0.79      inference('split', [status(esa)], ['0'])).
% 0.62/0.79  thf('3', plain,
% 0.62/0.79      (((r2_hidden @ sk_A @ sk_B)
% 0.62/0.79        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.62/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.79  thf('4', plain,
% 0.62/0.79      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('split', [status(esa)], ['3'])).
% 0.62/0.79  thf(t52_zfmisc_1, axiom,
% 0.62/0.79    (![A:$i,B:$i]:
% 0.62/0.79     ( ( r2_hidden @ A @ B ) =>
% 0.62/0.79       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.62/0.79  thf('5', plain,
% 0.62/0.79      (![X56 : $i, X57 : $i]:
% 0.62/0.79         (((k3_xboole_0 @ X57 @ (k1_tarski @ X56)) = (k1_tarski @ X56))
% 0.62/0.79          | ~ (r2_hidden @ X56 @ X57))),
% 0.62/0.79      inference('cnf', [status(esa)], [t52_zfmisc_1])).
% 0.62/0.79  thf('6', plain,
% 0.62/0.79      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup-', [status(thm)], ['4', '5'])).
% 0.62/0.79  thf(t100_xboole_1, axiom,
% 0.62/0.79    (![A:$i,B:$i]:
% 0.62/0.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.62/0.79  thf('7', plain,
% 0.62/0.79      (![X4 : $i, X5 : $i]:
% 0.62/0.79         ((k4_xboole_0 @ X4 @ X5)
% 0.62/0.79           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.62/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.79  thf('8', plain,
% 0.62/0.79      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.62/0.79          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['6', '7'])).
% 0.62/0.79  thf(commutativity_k5_xboole_0, axiom,
% 0.62/0.79    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.62/0.79  thf('9', plain,
% 0.62/0.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.79      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.79  thf(t95_xboole_1, axiom,
% 0.62/0.79    (![A:$i,B:$i]:
% 0.62/0.79     ( ( k3_xboole_0 @ A @ B ) =
% 0.62/0.79       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.62/0.79  thf('10', plain,
% 0.62/0.79      (![X16 : $i, X17 : $i]:
% 0.62/0.79         ((k3_xboole_0 @ X16 @ X17)
% 0.62/0.79           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.62/0.79              (k2_xboole_0 @ X16 @ X17)))),
% 0.62/0.79      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.62/0.79  thf('11', plain,
% 0.62/0.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.79      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.79  thf('12', plain,
% 0.62/0.79      (![X16 : $i, X17 : $i]:
% 0.62/0.79         ((k3_xboole_0 @ X16 @ X17)
% 0.62/0.79           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.62/0.79              (k5_xboole_0 @ X16 @ X17)))),
% 0.62/0.79      inference('demod', [status(thm)], ['10', '11'])).
% 0.62/0.79  thf('13', plain,
% 0.62/0.79      (![X0 : $i, X1 : $i]:
% 0.62/0.79         ((k3_xboole_0 @ X0 @ X1)
% 0.62/0.79           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['9', '12'])).
% 0.62/0.79  thf('14', plain,
% 0.62/0.79      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.62/0.79          = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.62/0.79             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['8', '13'])).
% 0.62/0.79  thf(commutativity_k2_tarski, axiom,
% 0.62/0.79    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.62/0.79  thf('15', plain,
% 0.62/0.79      (![X18 : $i, X19 : $i]:
% 0.62/0.79         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 0.62/0.79      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.62/0.79  thf(l51_zfmisc_1, axiom,
% 0.62/0.79    (![A:$i,B:$i]:
% 0.62/0.79     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.62/0.79  thf('16', plain,
% 0.62/0.79      (![X50 : $i, X51 : $i]:
% 0.62/0.79         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.62/0.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.62/0.79  thf('17', plain,
% 0.62/0.79      (![X0 : $i, X1 : $i]:
% 0.62/0.79         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.79      inference('sup+', [status(thm)], ['15', '16'])).
% 0.62/0.79  thf('18', plain,
% 0.62/0.79      (![X50 : $i, X51 : $i]:
% 0.62/0.79         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.62/0.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.62/0.79  thf('19', plain,
% 0.62/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.79      inference('sup+', [status(thm)], ['17', '18'])).
% 0.62/0.79  thf(t92_xboole_1, axiom,
% 0.62/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.62/0.79  thf('20', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.62/0.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.79  thf('21', plain,
% 0.62/0.79      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.62/0.79          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['6', '7'])).
% 0.62/0.79  thf('22', plain,
% 0.62/0.79      (![X16 : $i, X17 : $i]:
% 0.62/0.79         ((k3_xboole_0 @ X16 @ X17)
% 0.62/0.79           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.62/0.79              (k5_xboole_0 @ X16 @ X17)))),
% 0.62/0.79      inference('demod', [status(thm)], ['10', '11'])).
% 0.62/0.79  thf('23', plain,
% 0.62/0.79      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.62/0.79          = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.62/0.79             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['21', '22'])).
% 0.62/0.79  thf('24', plain,
% 0.62/0.79      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup-', [status(thm)], ['4', '5'])).
% 0.62/0.79  thf('25', plain,
% 0.62/0.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.79      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.79  thf('26', plain,
% 0.62/0.79      ((((k1_tarski @ sk_A)
% 0.62/0.79          = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.62/0.79             (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.62/0.79  thf('27', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.62/0.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.79  thf('28', plain,
% 0.62/0.79      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.62/0.79          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['6', '7'])).
% 0.62/0.79  thf(t91_xboole_1, axiom,
% 0.62/0.79    (![A:$i,B:$i,C:$i]:
% 0.62/0.79     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.62/0.79       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.62/0.79  thf('29', plain,
% 0.62/0.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.62/0.79         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.62/0.79           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.62/0.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.79  thf('30', plain,
% 0.62/0.79      ((![X0 : $i]:
% 0.62/0.79          ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.62/0.79            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['28', '29'])).
% 0.62/0.79  thf('31', plain,
% 0.62/0.79      ((((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.62/0.79          (k1_tarski @ sk_A)) = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['27', '30'])).
% 0.62/0.79  thf('32', plain,
% 0.62/0.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.79      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.79  thf('33', plain,
% 0.62/0.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.79      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.79  thf('34', plain,
% 0.62/0.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.79      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.79  thf(t5_boole, axiom,
% 0.62/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.62/0.79  thf('35', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.62/0.79      inference('cnf', [status(esa)], [t5_boole])).
% 0.62/0.79  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.79      inference('sup+', [status(thm)], ['34', '35'])).
% 0.62/0.79  thf('37', plain,
% 0.62/0.79      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.62/0.79          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B)))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('demod', [status(thm)], ['31', '32', '33', '36'])).
% 0.62/0.79  thf('38', plain,
% 0.62/0.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.62/0.79         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.62/0.79           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.62/0.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.79  thf('39', plain,
% 0.62/0.79      ((![X0 : $i]:
% 0.62/0.79          ((k5_xboole_0 @ sk_B @ X0)
% 0.62/0.79            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.62/0.79               (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['37', '38'])).
% 0.62/0.79  thf('40', plain,
% 0.62/0.79      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.62/0.79          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['26', '39'])).
% 0.62/0.79  thf('41', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.62/0.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.79  thf('42', plain,
% 0.62/0.79      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.62/0.79          = (k1_xboole_0)))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('demod', [status(thm)], ['40', '41'])).
% 0.62/0.79  thf('43', plain,
% 0.62/0.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.62/0.79         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.62/0.79           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.62/0.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.79  thf('44', plain,
% 0.62/0.79      ((![X0 : $i]:
% 0.62/0.79          ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.62/0.79            = (k5_xboole_0 @ sk_B @ 
% 0.62/0.79               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.62/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.79      inference('sup+', [status(thm)], ['42', '43'])).
% 0.62/0.79  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['34', '35'])).
% 0.62/0.80  thf('46', plain,
% 0.62/0.80      ((![X0 : $i]:
% 0.62/0.80          ((X0)
% 0.62/0.80            = (k5_xboole_0 @ sk_B @ 
% 0.62/0.80               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['44', '45'])).
% 0.62/0.80  thf('47', plain,
% 0.62/0.80      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.62/0.80          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['20', '46'])).
% 0.62/0.80  thf('48', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.80  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['34', '35'])).
% 0.62/0.80  thf('50', plain,
% 0.62/0.80      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.62/0.80  thf('51', plain,
% 0.62/0.80      (![X4 : $i, X5 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X4 @ X5)
% 0.62/0.80           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.80  thf('52', plain,
% 0.62/0.80      ((![X0 : $i]:
% 0.62/0.80          ((X0)
% 0.62/0.80            = (k5_xboole_0 @ sk_B @ 
% 0.62/0.80               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['44', '45'])).
% 0.62/0.80  thf('53', plain,
% 0.62/0.80      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.62/0.80  thf('54', plain,
% 0.62/0.80      ((![X0 : $i]: ((X0) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0))))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['52', '53'])).
% 0.62/0.80  thf('55', plain,
% 0.62/0.80      ((![X0 : $i]:
% 0.62/0.80          ((k3_xboole_0 @ sk_B @ X0)
% 0.62/0.80            = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0))))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['51', '54'])).
% 0.62/0.80  thf('56', plain,
% 0.62/0.80      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.62/0.80          = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['14', '19', '50', '55'])).
% 0.62/0.80  thf('57', plain,
% 0.62/0.80      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.62/0.80  thf('58', plain,
% 0.62/0.80      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['56', '57'])).
% 0.62/0.80  thf('59', plain,
% 0.62/0.80      (![X4 : $i, X5 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X4 @ X5)
% 0.62/0.80           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.80  thf('60', plain,
% 0.62/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.62/0.80          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['58', '59'])).
% 0.62/0.80  thf('61', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.62/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.80  thf('62', plain,
% 0.62/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.62/0.80         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['60', '61'])).
% 0.62/0.80  thf('63', plain,
% 0.62/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.62/0.80         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.62/0.80      inference('split', [status(esa)], ['0'])).
% 0.62/0.80  thf('64', plain,
% 0.62/0.80      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.62/0.80         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.62/0.80             ((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['62', '63'])).
% 0.62/0.80  thf('65', plain,
% 0.62/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.62/0.80       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.62/0.80      inference('simplify', [status(thm)], ['64'])).
% 0.62/0.80  thf('66', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.62/0.80      inference('sat_resolution*', [status(thm)], ['2', '65'])).
% 0.62/0.80  thf('67', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.62/0.80      inference('simpl_trail', [status(thm)], ['1', '66'])).
% 0.62/0.80  thf('68', plain,
% 0.62/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.62/0.80         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.62/0.80      inference('split', [status(esa)], ['3'])).
% 0.62/0.80  thf('69', plain,
% 0.62/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.62/0.80       ((r2_hidden @ sk_A @ sk_B))),
% 0.62/0.80      inference('split', [status(esa)], ['3'])).
% 0.62/0.80  thf('70', plain,
% 0.62/0.80      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.62/0.80      inference('sat_resolution*', [status(thm)], ['2', '65', '69'])).
% 0.62/0.80  thf('71', plain,
% 0.62/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.62/0.80      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 0.62/0.80  thf('72', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k3_xboole_0 @ X0 @ X1)
% 0.62/0.80           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['9', '12'])).
% 0.62/0.80  thf('73', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.80  thf('74', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.62/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.80  thf('75', plain,
% 0.62/0.80      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.62/0.80           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.80  thf('76', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.62/0.80           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['74', '75'])).
% 0.62/0.80  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['34', '35'])).
% 0.62/0.80  thf('78', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['76', '77'])).
% 0.62/0.80  thf('79', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['73', '78'])).
% 0.62/0.80  thf('80', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ X1 @ X0)
% 0.62/0.80           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['72', '79'])).
% 0.62/0.80  thf('81', plain,
% 0.62/0.80      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 0.62/0.80           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.80  thf('82', plain,
% 0.62/0.80      (![X4 : $i, X5 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X4 @ X5)
% 0.62/0.80           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.80  thf('83', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ X1 @ X0)
% 0.62/0.80           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.62/0.80  thf('84', plain,
% 0.62/0.80      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.62/0.80         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['71', '83'])).
% 0.62/0.80  thf('85', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.62/0.80  thf('86', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.80  thf('87', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['34', '35'])).
% 0.62/0.80  thf('88', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.62/0.80      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.62/0.80  thf('89', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.62/0.80  thf(t69_enumset1, axiom,
% 0.62/0.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.62/0.80  thf('90', plain,
% 0.62/0.80      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.62/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.80  thf(t31_zfmisc_1, axiom,
% 0.62/0.80    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.62/0.80  thf('91', plain, (![X55 : $i]: ((k3_tarski @ (k1_tarski @ X55)) = (X55))),
% 0.62/0.80      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.62/0.80  thf('92', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['90', '91'])).
% 0.62/0.80  thf('93', plain,
% 0.62/0.80      (![X50 : $i, X51 : $i]:
% 0.62/0.80         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.62/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.62/0.80  thf('94', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['92', '93'])).
% 0.62/0.80  thf(t4_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.62/0.80       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.62/0.80  thf('95', plain,
% 0.62/0.80      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 0.62/0.80           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.62/0.80  thf('96', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ X0 @ X1)
% 0.62/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['94', '95'])).
% 0.62/0.80  thf(l27_zfmisc_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.62/0.80  thf('97', plain,
% 0.62/0.80      (![X48 : $i, X49 : $i]:
% 0.62/0.80         ((r1_xboole_0 @ (k1_tarski @ X48) @ X49) | (r2_hidden @ X48 @ X49))),
% 0.62/0.80      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.62/0.80  thf(t88_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( r1_xboole_0 @ A @ B ) =>
% 0.62/0.80       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.62/0.80  thf('98', plain,
% 0.62/0.80      (![X10 : $i, X11 : $i]:
% 0.62/0.80         (((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11) = (X10))
% 0.62/0.80          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.62/0.80      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.62/0.80  thf('99', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((r2_hidden @ X1 @ X0)
% 0.62/0.80          | ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X0)
% 0.62/0.80              = (k1_tarski @ X1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['97', '98'])).
% 0.62/0.80  thf('100', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ 
% 0.62/0.80            (k2_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k1_tarski @ X1))
% 0.62/0.80          | (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['96', '99'])).
% 0.62/0.80  thf('101', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['92', '93'])).
% 0.62/0.80  thf('102', plain,
% 0.62/0.80      (![X16 : $i, X17 : $i]:
% 0.62/0.80         ((k3_xboole_0 @ X16 @ X17)
% 0.62/0.80           = (k5_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ 
% 0.62/0.80              (k5_xboole_0 @ X16 @ X17)))),
% 0.62/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.62/0.80  thf('103', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         ((k3_xboole_0 @ X0 @ X0)
% 0.62/0.80           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['101', '102'])).
% 0.62/0.80  thf('104', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.62/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.80  thf('105', plain,
% 0.62/0.80      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.80      inference('demod', [status(thm)], ['103', '104'])).
% 0.62/0.80  thf('106', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.62/0.80      inference('cnf', [status(esa)], [t5_boole])).
% 0.62/0.80  thf('107', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['105', '106'])).
% 0.62/0.80  thf('108', plain,
% 0.62/0.80      (![X4 : $i, X5 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X4 @ X5)
% 0.62/0.80           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.80  thf('109', plain,
% 0.62/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['107', '108'])).
% 0.62/0.80  thf('110', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 0.62/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.80  thf('111', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['109', '110'])).
% 0.62/0.80  thf('112', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (((k1_xboole_0) = (k1_tarski @ X1))
% 0.62/0.80          | (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['100', '111'])).
% 0.62/0.80  thf(t20_zfmisc_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.62/0.80         ( k1_tarski @ A ) ) <=>
% 0.62/0.80       ( ( A ) != ( B ) ) ))).
% 0.62/0.80  thf('113', plain,
% 0.62/0.80      (![X52 : $i, X53 : $i]:
% 0.62/0.80         (((X53) != (X52))
% 0.62/0.80          | ((k4_xboole_0 @ (k1_tarski @ X53) @ (k1_tarski @ X52))
% 0.62/0.80              != (k1_tarski @ X53)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.62/0.80  thf('114', plain,
% 0.62/0.80      (![X52 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ (k1_tarski @ X52) @ (k1_tarski @ X52))
% 0.62/0.80           != (k1_tarski @ X52))),
% 0.62/0.80      inference('simplify', [status(thm)], ['113'])).
% 0.62/0.80  thf('115', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['109', '110'])).
% 0.62/0.80  thf('116', plain, (![X52 : $i]: ((k1_xboole_0) != (k1_tarski @ X52))),
% 0.62/0.80      inference('demod', [status(thm)], ['114', '115'])).
% 0.62/0.80  thf('117', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.62/0.80      inference('clc', [status(thm)], ['112', '116'])).
% 0.62/0.80  thf('118', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['89', '117'])).
% 0.62/0.80  thf('119', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.62/0.80      inference('sup+', [status(thm)], ['88', '118'])).
% 0.62/0.80  thf('120', plain, ($false), inference('demod', [status(thm)], ['67', '119'])).
% 0.62/0.80  
% 0.62/0.80  % SZS output end Refutation
% 0.62/0.80  
% 0.62/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
