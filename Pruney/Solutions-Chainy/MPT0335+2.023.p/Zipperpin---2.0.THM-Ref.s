%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDlezd1Y4j

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:15 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 257 expanded)
%              Number of leaves         :   24 (  92 expanded)
%              Depth                    :   13
%              Number of atoms          :  816 (2091 expanded)
%              Number of equality atoms :   95 ( 235 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X44 ) @ X43 )
        = X43 )
      | ~ ( r2_hidden @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('14',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['4','24'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X3 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('53',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['33','34','58','78'])).

thf('80',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDlezd1Y4j
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.81  % Solved by: fo/fo7.sh
% 0.61/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.81  % done 885 iterations in 0.358s
% 0.61/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.81  % SZS output start Refutation
% 0.61/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.61/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.81  thf(t148_zfmisc_1, conjecture,
% 0.61/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.81     ( ( ( r1_tarski @ A @ B ) & 
% 0.61/0.81         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.61/0.81         ( r2_hidden @ D @ A ) ) =>
% 0.61/0.81       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.61/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.81    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.81        ( ( ( r1_tarski @ A @ B ) & 
% 0.61/0.81            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.61/0.81            ( r2_hidden @ D @ A ) ) =>
% 0.61/0.81          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.61/0.81    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.61/0.81  thf('0', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t46_zfmisc_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r2_hidden @ A @ B ) =>
% 0.61/0.81       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.61/0.81  thf('1', plain,
% 0.61/0.81      (![X43 : $i, X44 : $i]:
% 0.61/0.81         (((k2_xboole_0 @ (k1_tarski @ X44) @ X43) = (X43))
% 0.61/0.81          | ~ (r2_hidden @ X44 @ X43))),
% 0.61/0.81      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.61/0.81  thf('2', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['0', '1'])).
% 0.61/0.81  thf(t40_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('3', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.61/0.81           = (k4_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('4', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_A @ sk_A)
% 0.61/0.81         = (k4_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A))),
% 0.61/0.81      inference('sup+', [status(thm)], ['2', '3'])).
% 0.61/0.81  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t12_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.61/0.81  thf('6', plain,
% 0.61/0.81      (![X6 : $i, X7 : $i]:
% 0.61/0.81         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.61/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.61/0.81  thf('7', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.61/0.81      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.81  thf('8', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.61/0.81           = (k4_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('9', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.81      inference('sup+', [status(thm)], ['7', '8'])).
% 0.61/0.81  thf(t39_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('10', plain,
% 0.61/0.81      (![X14 : $i, X15 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.61/0.81           = (k2_xboole_0 @ X14 @ X15))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('11', plain,
% 0.61/0.81      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_B))
% 0.61/0.81         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.61/0.81      inference('sup+', [status(thm)], ['9', '10'])).
% 0.61/0.81  thf('12', plain,
% 0.61/0.81      (![X14 : $i, X15 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.61/0.81           = (k2_xboole_0 @ X14 @ X15))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf(idempotence_k2_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.61/0.81  thf('13', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.61/0.81      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.61/0.81  thf('14', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.61/0.81  thf(t36_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.81  thf('15', plain,
% 0.61/0.81      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.61/0.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.81  thf('16', plain,
% 0.61/0.81      (![X6 : $i, X7 : $i]:
% 0.61/0.81         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.61/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.61/0.81  thf('17', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.81  thf('18', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.61/0.81           = (k4_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('19', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X0 @ X0)
% 0.61/0.81           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['17', '18'])).
% 0.61/0.81  thf(t41_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.81       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.61/0.81  thf('20', plain,
% 0.61/0.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.61/0.81           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.61/0.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.61/0.81  thf('21', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X0 @ X0)
% 0.61/0.81           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['19', '20'])).
% 0.61/0.81  thf('22', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.81      inference('sup+', [status(thm)], ['14', '21'])).
% 0.61/0.81  thf('23', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.81      inference('sup+', [status(thm)], ['7', '8'])).
% 0.61/0.81  thf('24', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_B @ sk_B))),
% 0.61/0.81      inference('demod', [status(thm)], ['22', '23'])).
% 0.61/0.81  thf('25', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_B @ sk_B)
% 0.61/0.81         = (k4_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['4', '24'])).
% 0.61/0.81  thf(t47_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('26', plain,
% 0.61/0.81      (![X23 : $i, X24 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.61/0.81           = (k4_xboole_0 @ X23 @ X24))),
% 0.61/0.81      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.61/0.81  thf('27', plain,
% 0.61/0.81      (![X14 : $i, X15 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.61/0.81           = (k2_xboole_0 @ X14 @ X15))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('28', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['26', '27'])).
% 0.61/0.81  thf(t48_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.61/0.81  thf('29', plain,
% 0.61/0.81      (![X25 : $i, X26 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.61/0.81           = (k3_xboole_0 @ X25 @ X26))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('30', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.61/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.81  thf('31', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['29', '30'])).
% 0.61/0.81  thf('32', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (X1))),
% 0.61/0.81      inference('demod', [status(thm)], ['28', '31'])).
% 0.61/0.81  thf('33', plain,
% 0.61/0.81      (((k2_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) @ 
% 0.61/0.81         (k4_xboole_0 @ sk_B @ sk_B)) = (k1_tarski @ sk_D_1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['25', '32'])).
% 0.61/0.81  thf(commutativity_k3_xboole_0, axiom,
% 0.61/0.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.61/0.81  thf('34', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('35', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D_1))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('36', plain,
% 0.61/0.81      (![X23 : $i, X24 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.61/0.81           = (k4_xboole_0 @ X23 @ X24))),
% 0.61/0.81      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.61/0.81  thf('37', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1))
% 0.61/0.81         = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.61/0.81      inference('sup+', [status(thm)], ['35', '36'])).
% 0.61/0.81  thf('38', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf(t28_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i]:
% 0.61/0.81     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.61/0.81  thf('39', plain,
% 0.61/0.81      (![X8 : $i, X9 : $i]:
% 0.61/0.81         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.61/0.81      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.61/0.81  thf('40', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.61/0.81      inference('sup-', [status(thm)], ['38', '39'])).
% 0.61/0.81  thf('41', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('42', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.61/0.81      inference('demod', [status(thm)], ['40', '41'])).
% 0.61/0.81  thf(t111_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.61/0.81       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.61/0.81  thf('43', plain,
% 0.61/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k3_xboole_0 @ X3 @ X5) @ (k3_xboole_0 @ X4 @ X5))
% 0.61/0.81           = (k3_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5))),
% 0.61/0.81      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.61/0.81  thf('44', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_A))
% 0.61/0.81           = (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.61/0.81      inference('sup+', [status(thm)], ['42', '43'])).
% 0.61/0.81  thf('45', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('46', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_A))
% 0.61/0.81           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['44', '45'])).
% 0.61/0.81  thf('47', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('48', plain,
% 0.61/0.81      (![X23 : $i, X24 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.61/0.81           = (k4_xboole_0 @ X23 @ X24))),
% 0.61/0.81      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.61/0.81  thf('49', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k4_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['47', '48'])).
% 0.61/0.81  thf('50', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ sk_A @ X0)
% 0.61/0.81           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['46', '49'])).
% 0.61/0.81  thf('51', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 0.61/0.81         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['37', '50'])).
% 0.61/0.81  thf('52', plain,
% 0.61/0.81      (![X0 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ sk_A @ X0)
% 0.61/0.81           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['46', '49'])).
% 0.61/0.81  thf('53', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 0.61/0.81         = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.61/0.81      inference('demod', [status(thm)], ['51', '52'])).
% 0.61/0.81  thf('54', plain,
% 0.61/0.81      (![X25 : $i, X26 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.61/0.81           = (k3_xboole_0 @ X25 @ X26))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('55', plain,
% 0.61/0.81      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.61/0.81         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['53', '54'])).
% 0.61/0.81  thf('56', plain,
% 0.61/0.81      (![X25 : $i, X26 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.61/0.81           = (k3_xboole_0 @ X25 @ X26))),
% 0.61/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.81  thf('57', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('58', plain,
% 0.61/0.81      (((k3_xboole_0 @ sk_C @ sk_A)
% 0.61/0.81         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 0.61/0.81      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.61/0.81  thf('59', plain,
% 0.61/0.81      (![X14 : $i, X15 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.61/0.81           = (k2_xboole_0 @ X14 @ X15))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('60', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('61', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['29', '30'])).
% 0.61/0.81  thf('62', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['60', '61'])).
% 0.61/0.81  thf('63', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.61/0.81           = (k4_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('64', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X0 @ X0)
% 0.61/0.81           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.61/0.81      inference('sup+', [status(thm)], ['62', '63'])).
% 0.61/0.81  thf(t49_xboole_1, axiom,
% 0.61/0.81    (![A:$i,B:$i,C:$i]:
% 0.61/0.81     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.61/0.81       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.61/0.81  thf('65', plain,
% 0.61/0.81      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.61/0.81         ((k3_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 0.61/0.81           = (k4_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ X29))),
% 0.61/0.81      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.61/0.81  thf('66', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ X0 @ X0)
% 0.61/0.81           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.61/0.81      inference('demod', [status(thm)], ['64', '65'])).
% 0.61/0.81  thf('67', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['29', '30'])).
% 0.61/0.81  thf('68', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['66', '67'])).
% 0.61/0.81  thf('69', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.61/0.81           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['59', '68'])).
% 0.61/0.81  thf('70', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['66', '67'])).
% 0.61/0.81  thf('71', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)))),
% 0.61/0.81      inference('demod', [status(thm)], ['69', '70'])).
% 0.61/0.81  thf('72', plain,
% 0.61/0.81      (![X16 : $i, X17 : $i]:
% 0.61/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.61/0.81           = (k4_xboole_0 @ X16 @ X17))),
% 0.61/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.81  thf('73', plain,
% 0.61/0.81      (![X14 : $i, X15 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.61/0.81           = (k2_xboole_0 @ X14 @ X15))),
% 0.61/0.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.81  thf('74', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.61/0.81           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.61/0.81      inference('sup+', [status(thm)], ['72', '73'])).
% 0.61/0.81  thf('75', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.61/0.81           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ 
% 0.61/0.81              (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1))))),
% 0.61/0.81      inference('sup+', [status(thm)], ['71', '74'])).
% 0.61/0.81  thf('76', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['66', '67'])).
% 0.61/0.81  thf('77', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.61/0.81      inference('sup+', [status(thm)], ['66', '67'])).
% 0.61/0.81  thf('78', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]:
% 0.61/0.81         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)))),
% 0.61/0.81      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.61/0.81  thf('79', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D_1))),
% 0.61/0.81      inference('demod', [status(thm)], ['33', '34', '58', '78'])).
% 0.61/0.81  thf('80', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D_1))),
% 0.61/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.81  thf('81', plain,
% 0.61/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.81  thf('82', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D_1))),
% 0.61/0.81      inference('demod', [status(thm)], ['80', '81'])).
% 0.61/0.81  thf('83', plain, ($false),
% 0.61/0.81      inference('simplify_reflect-', [status(thm)], ['79', '82'])).
% 0.61/0.81  
% 0.61/0.81  % SZS output end Refutation
% 0.61/0.81  
% 0.61/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
