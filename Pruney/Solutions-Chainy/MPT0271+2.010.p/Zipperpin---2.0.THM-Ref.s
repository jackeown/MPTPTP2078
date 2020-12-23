%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SJZtxqfrH1

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:21 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 451 expanded)
%              Number of leaves         :   27 ( 153 expanded)
%              Depth                    :   26
%              Number of atoms          : 1132 (3766 expanded)
%              Number of equality atoms :  124 ( 427 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X51: $i,X52: $i] :
      ( ( ( k3_xboole_0 @ X52 @ ( k1_tarski @ X51 ) )
        = ( k1_tarski @ X51 ) )
      | ~ ( r2_hidden @ X51 @ X52 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
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
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
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
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
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
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
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
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('42',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
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

thf('51',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','19','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','61'])).

thf('63',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','62'])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','61','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('70',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('71',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','75'])).

thf('77',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('78',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('86',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('87',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('89',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X49 ) @ X50 )
      | ( r2_hidden @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('90',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('94',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','103'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('105',plain,(
    ! [X55: $i,X56: $i] :
      ( ( X56 != X55 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X56 ) @ ( k1_tarski @ X55 ) )
       != ( k1_tarski @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('106',plain,(
    ! [X55: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X55 ) @ ( k1_tarski @ X55 ) )
     != ( k1_tarski @ X55 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('108',plain,(
    ! [X55: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X55 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['104','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','109'])).

thf('111',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['84','110'])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['63','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SJZtxqfrH1
% 0.11/0.31  % Computer   : n013.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 20:55:10 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.32  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 627 iterations in 0.236s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.66  thf(t68_zfmisc_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.66       ( r2_hidden @ A @ B ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i]:
% 0.46/0.66        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.66          ( r2_hidden @ A @ B ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.46/0.66        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.46/0.66       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (((r2_hidden @ sk_A @ sk_B)
% 0.46/0.66        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('split', [status(esa)], ['3'])).
% 0.46/0.66  thf(l31_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.66       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X51 : $i, X52 : $i]:
% 0.46/0.66         (((k3_xboole_0 @ X52 @ (k1_tarski @ X51)) = (k1_tarski @ X51))
% 0.46/0.66          | ~ (r2_hidden @ X51 @ X52))),
% 0.46/0.66      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf(t100_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.66          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(commutativity_k5_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf(t95_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k3_xboole_0 @ A @ B ) =
% 0.46/0.66       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X17 @ X18)
% 0.46/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.46/0.66              (k2_xboole_0 @ X17 @ X18)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X17 @ X18)
% 0.46/0.66           = (k5_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 0.46/0.66              (k5_xboole_0 @ X17 @ X18)))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['9', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.66          = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.46/0.66             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['8', '13'])).
% 0.46/0.66  thf(commutativity_k2_tarski, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X19 : $i, X20 : $i]:
% 0.46/0.66         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.66  thf(l51_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X53 : $i, X54 : $i]:
% 0.46/0.66         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.46/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X53 : $i, X54 : $i]:
% 0.46/0.66         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.46/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.66  thf(t92_xboole_1, axiom,
% 0.46/0.66    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.66  thf('20', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.66          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X17 @ X18)
% 0.46/0.66           = (k5_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 0.46/0.66              (k5_xboole_0 @ X17 @ X18)))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.66          = (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      ((((k1_tarski @ sk_A)
% 0.46/0.66          = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66             (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.46/0.66  thf('27', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.66          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(t91_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.66       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.46/0.66            = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      ((((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.66          (k1_tarski @ sk_A)) = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['27', '30'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf(t5_boole, axiom,
% 0.46/0.66    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.66  thf('35', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.66  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      ((((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B)))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['31', '32', '33', '36'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          ((k5_xboole_0 @ sk_B @ X0)
% 0.46/0.66            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66               (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.66          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['26', '39'])).
% 0.46/0.66  thf('41', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      ((((k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.66          = (k1_xboole_0)))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66            = (k5_xboole_0 @ sk_B @ 
% 0.46/0.66               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          ((X0)
% 0.46/0.66            = (k5_xboole_0 @ sk_B @ 
% 0.46/0.66               (k5_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['44', '45'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.66          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['20', '46'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.66          = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['14', '19', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          ((k5_xboole_0 @ sk_B @ X0)
% 0.46/0.66            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66               (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      ((![X0 : $i]:
% 0.46/0.66          ((k5_xboole_0 @ sk_B @ X0)
% 0.46/0.66            = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66               (k5_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      ((((k5_xboole_0 @ sk_B @ sk_B)
% 0.46/0.66          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.66             (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['51', '54'])).
% 0.46/0.66  thf('56', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      ((((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.46/0.66         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.46/0.66         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.66         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.46/0.66             ((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.46/0.66       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.46/0.66      inference('simplify', [status(thm)], ['60'])).
% 0.46/0.66  thf('62', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['2', '61'])).
% 0.46/0.66  thf('63', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['1', '62'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.46/0.66         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.46/0.66      inference('split', [status(esa)], ['3'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.46/0.66       ((r2_hidden @ sk_A @ sk_B))),
% 0.46/0.66      inference('split', [status(esa)], ['3'])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['2', '61', '65'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['64', '66'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['9', '12'])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf('70', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('73', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.66  thf('75', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['69', '74'])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X1 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['68', '75'])).
% 0.46/0.66  thf('77', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.66  thf('78', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('79', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X1 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.66         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['67', '79'])).
% 0.46/0.66  thf('81', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.66  thf('83', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.66  thf('84', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.66  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.66  thf('86', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.66  thf(t4_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.66       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.46/0.66           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.46/0.66  thf('88', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.66           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['86', '87'])).
% 0.46/0.66  thf(l27_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      (![X49 : $i, X50 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ (k1_tarski @ X49) @ X50) | (r2_hidden @ X49 @ X50))),
% 0.46/0.66      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.46/0.66  thf(t88_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( r1_xboole_0 @ A @ B ) =>
% 0.46/0.66       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12) = (X11))
% 0.46/0.66          | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ X1 @ X0)
% 0.46/0.66          | ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X0)
% 0.46/0.66              = (k1_tarski @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['89', '90'])).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ 
% 0.46/0.66            (k2_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k1_tarski @ X1))
% 0.46/0.66          | (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['88', '91'])).
% 0.46/0.66  thf('93', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.66  thf('94', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X17 @ X18)
% 0.46/0.66           = (k5_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 0.46/0.66              (k5_xboole_0 @ X17 @ X18)))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.66  thf('95', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X0 @ X0)
% 0.46/0.66           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['93', '94'])).
% 0.46/0.66  thf('96', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['95', '96'])).
% 0.46/0.66  thf('98', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.66  thf('99', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['97', '98'])).
% 0.46/0.66  thf('100', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.66           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.66  thf('101', plain,
% 0.46/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['99', '100'])).
% 0.46/0.66  thf('102', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.66  thf('103', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['101', '102'])).
% 0.46/0.66  thf('104', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (k1_tarski @ X1))
% 0.46/0.66          | (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['92', '103'])).
% 0.46/0.66  thf(t20_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.46/0.66         ( k1_tarski @ A ) ) <=>
% 0.46/0.66       ( ( A ) != ( B ) ) ))).
% 0.46/0.66  thf('105', plain,
% 0.46/0.66      (![X55 : $i, X56 : $i]:
% 0.46/0.66         (((X56) != (X55))
% 0.46/0.66          | ((k4_xboole_0 @ (k1_tarski @ X56) @ (k1_tarski @ X55))
% 0.46/0.66              != (k1_tarski @ X56)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.46/0.66  thf('106', plain,
% 0.46/0.66      (![X55 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k1_tarski @ X55) @ (k1_tarski @ X55))
% 0.46/0.66           != (k1_tarski @ X55))),
% 0.46/0.66      inference('simplify', [status(thm)], ['105'])).
% 0.46/0.66  thf('107', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['101', '102'])).
% 0.46/0.66  thf('108', plain, (![X55 : $i]: ((k1_xboole_0) != (k1_tarski @ X55))),
% 0.46/0.66      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.66  thf('109', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.46/0.66      inference('clc', [status(thm)], ['104', '108'])).
% 0.46/0.66  thf('110', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['85', '109'])).
% 0.46/0.66  thf('111', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.66      inference('sup+', [status(thm)], ['84', '110'])).
% 0.46/0.66  thf('112', plain, ($false), inference('demod', [status(thm)], ['63', '111'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
