%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WanLsDJaKP

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:55 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  157 (1448 expanded)
%              Number of leaves         :   25 ( 467 expanded)
%              Depth                    :   28
%              Number of atoms          : 1227 (10633 expanded)
%              Number of equality atoms :  133 (1229 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X36: $i,X38: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X36 ) @ X38 )
      | ~ ( r2_hidden @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('13',plain,(
    r1_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('41',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','33','43'])).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','33','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('48',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('55',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ X0 ) @ X1 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) )
      = sk_B ) ),
    inference('sup+',[status(thm)],['63','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ sk_B ) ) ) )
      = sk_B ) ),
    inference('sup+',[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) )
      = sk_B ) ),
    inference('sup+',[status(thm)],['63','72'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ sk_B ) ) ) @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ) ) )
      = sk_B ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('78',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('79',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('85',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ X0 ) ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['23','24','93'])).

thf('95',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('97',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('106',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['110','113','114'])).

thf('116',plain,
    ( ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['95','115'])).

thf('117',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('120',plain,
    ( ( k1_tarski @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('122',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('126',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('129',plain,(
    ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['126','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WanLsDJaKP
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:49:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 325 iterations in 0.222s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(t140_zfmisc_1, conjecture,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.68       ( ( k2_xboole_0 @
% 0.46/0.68           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.46/0.68         ( B ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i]:
% 0.46/0.68        ( ( r2_hidden @ A @ B ) =>
% 0.46/0.68          ( ( k2_xboole_0 @
% 0.46/0.68              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.46/0.68            ( B ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.46/0.68  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(l1_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      (![X36 : $i, X38 : $i]:
% 0.46/0.68         ((r1_tarski @ (k1_tarski @ X36) @ X38) | ~ (r2_hidden @ X36 @ X38))),
% 0.46/0.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.46/0.68  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.68  thf(t28_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('4', plain,
% 0.46/0.68      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.68  thf(t100_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X8 : $i, X9 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.46/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.68         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf(t39_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.46/0.68           = (k2_xboole_0 @ X13 @ X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.68         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.68         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf(t79_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.46/0.68      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      ((r1_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.68        (k1_tarski @ sk_A))),
% 0.46/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.68  thf(t83_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X18 : $i, X19 : $i]:
% 0.46/0.68         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.46/0.68      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (((k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.68         (k1_tarski @ sk_A)) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf(t94_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k2_xboole_0 @ A @ B ) =
% 0.46/0.68       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X24 @ X25)
% 0.46/0.68           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.46/0.68              (k3_xboole_0 @ X24 @ X25)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.68  thf(t91_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.68       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X24 @ X25)
% 0.46/0.68           = (k5_xboole_0 @ X24 @ 
% 0.46/0.68              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.46/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.68           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['16', '19'])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X8 : $i, X9 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.46/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.68           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.68         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.68            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['15', '22'])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.46/0.68         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X24 @ X25)
% 0.46/0.68           = (k5_xboole_0 @ X24 @ 
% 0.46/0.68              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.46/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X24 @ X25)
% 0.46/0.68           = (k5_xboole_0 @ X24 @ 
% 0.46/0.68              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.46/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.68         = (k5_xboole_0 @ sk_B @ 
% 0.46/0.68            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.68  thf('29', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.68  thf(l32_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (![X5 : $i, X7 : $i]:
% 0.46/0.68         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.46/0.68           = (k2_xboole_0 @ X13 @ X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.46/0.68         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.68  thf(d10_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.68  thf('35', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.46/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('37', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      (![X8 : $i, X9 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.46/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.68  thf('40', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.46/0.68      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      (![X5 : $i, X7 : $i]:
% 0.46/0.68         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.46/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.68  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['39', '42'])).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '33', '43'])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('46', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ X0)
% 0.46/0.68           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['44', '45'])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '33', '43'])).
% 0.46/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.68  thf('48', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.68  thf('53', plain,
% 0.46/0.68      (![X8 : $i, X9 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.46/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.68  thf(t3_boole, axiom,
% 0.46/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.68  thf('55', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.68  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('57', plain, (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['47', '56'])).
% 0.46/0.68  thf('58', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ X0)
% 0.46/0.68           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['46', '57'])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ 
% 0.46/0.68           (k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 0.46/0.68           = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['25', '58'])).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.68  thf('61', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('62', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ X0)
% 0.46/0.68           = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('64', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['39', '42'])).
% 0.46/0.68  thf('65', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ X0)
% 0.46/0.68           = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.46/0.68  thf('66', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ sk_B @ X0) @ X1)
% 0.46/0.68           = (k5_xboole_0 @ sk_B @ 
% 0.46/0.68              (k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X1)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['65', '66'])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ X1))
% 0.46/0.68           = (k5_xboole_0 @ sk_B @ 
% 0.46/0.68              (k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.68  thf('70', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ 
% 0.46/0.68           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))
% 0.46/0.68           = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['64', '69'])).
% 0.46/0.68  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('72', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ 
% 0.46/0.68           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0))) = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['70', '71'])).
% 0.46/0.68  thf('73', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ 
% 0.46/0.68           (k5_xboole_0 @ X1 @ 
% 0.46/0.68            (k5_xboole_0 @ X0 @ 
% 0.46/0.68             (k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X1 @ X0)))))
% 0.46/0.68           = (sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['63', '72'])).
% 0.46/0.68  thf('74', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ 
% 0.46/0.68           (k5_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ sk_B))))
% 0.46/0.68           = (sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['62', '73'])).
% 0.46/0.68  thf('75', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ 
% 0.46/0.68           (k5_xboole_0 @ X1 @ 
% 0.46/0.68            (k5_xboole_0 @ X0 @ 
% 0.46/0.68             (k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X1 @ X0)))))
% 0.46/0.68           = (sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['63', '72'])).
% 0.46/0.68  thf('76', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ 
% 0.46/0.68           (k5_xboole_0 @ sk_B @ 
% 0.46/0.68            (k5_xboole_0 @ 
% 0.46/0.68             (k5_xboole_0 @ X0 @ 
% 0.46/0.68              (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ sk_B))) @ 
% 0.46/0.68             (k2_xboole_0 @ k1_xboole_0 @ sk_B))))
% 0.46/0.68           = (sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['74', '75'])).
% 0.46/0.68  thf('77', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('78', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('79', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('80', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ X0)
% 0.46/0.68           = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.46/0.68  thf('81', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['39', '42'])).
% 0.46/0.68  thf('82', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('83', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ sk_B @ 
% 0.46/0.68           (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ X0))))
% 0.46/0.68           = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)],
% 0.46/0.68                ['76', '77', '78', '79', '80', '81', '82'])).
% 0.46/0.68  thf('84', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['39', '42'])).
% 0.46/0.68  thf('85', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('86', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.68  thf('87', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.68           (k5_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ X0))) = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['83', '86'])).
% 0.46/0.68  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['39', '42'])).
% 0.46/0.68  thf('89', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.68  thf('90', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['88', '89'])).
% 0.46/0.68  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('92', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.68  thf('93', plain,
% 0.46/0.68      (![X0 : $i]: ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ X0)) = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['87', '92'])).
% 0.46/0.68  thf('94', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['23', '24', '93'])).
% 0.46/0.68  thf('95', plain,
% 0.46/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.68         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '94'])).
% 0.46/0.68  thf('96', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['39', '42'])).
% 0.46/0.68  thf('97', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('98', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k1_xboole_0)
% 0.46/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['96', '97'])).
% 0.46/0.68  thf('99', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.68  thf('100', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.68  thf('101', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['99', '100'])).
% 0.46/0.68  thf('102', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.46/0.68           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['98', '101'])).
% 0.46/0.68  thf('103', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('104', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.46/0.68      inference('demod', [status(thm)], ['102', '103'])).
% 0.46/0.68  thf('105', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X24 @ X25)
% 0.46/0.68           = (k5_xboole_0 @ X24 @ 
% 0.46/0.68              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.46/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.46/0.68  thf('106', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('107', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.68           = (k5_xboole_0 @ X1 @ 
% 0.46/0.68              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['105', '106'])).
% 0.46/0.68  thf('108', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('109', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.68           = (k5_xboole_0 @ X1 @ 
% 0.46/0.68              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))))),
% 0.46/0.68      inference('demod', [status(thm)], ['107', '108'])).
% 0.46/0.68  thf('110', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.68           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['104', '109'])).
% 0.46/0.68  thf('111', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.46/0.68      inference('demod', [status(thm)], ['102', '103'])).
% 0.46/0.68  thf('112', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['99', '100'])).
% 0.46/0.68  thf('113', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['111', '112'])).
% 0.46/0.68  thf('114', plain,
% 0.46/0.68      (![X8 : $i, X9 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X8 @ X9)
% 0.46/0.68           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.68  thf('115', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.46/0.68           = (k4_xboole_0 @ X1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['110', '113', '114'])).
% 0.46/0.68  thf('116', plain,
% 0.46/0.68      (((k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 0.46/0.68         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.68            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.68      inference('sup+', [status(thm)], ['95', '115'])).
% 0.46/0.68  thf('117', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('118', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['111', '112'])).
% 0.46/0.68  thf('119', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['99', '100'])).
% 0.46/0.68  thf('120', plain,
% 0.46/0.68      (((k1_tarski @ sk_A)
% 0.46/0.68         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.46/0.68            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.46/0.68      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.46/0.68  thf('121', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.68           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.68  thf('122', plain,
% 0.46/0.68      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.68         (k1_tarski @ sk_A))
% 0.46/0.68         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.68            (k1_tarski @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['120', '121'])).
% 0.46/0.68  thf('123', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.46/0.68           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.68  thf('124', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['39', '42'])).
% 0.46/0.68  thf('125', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('126', plain,
% 0.46/0.68      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.68         (k1_tarski @ sk_A)) = (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 0.46/0.68  thf('127', plain,
% 0.46/0.68      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.68         (k1_tarski @ sk_A)) != (sk_B))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('128', plain,
% 0.46/0.68      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.68         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf('129', plain,
% 0.46/0.68      (((k2_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.46/0.68         (k1_tarski @ sk_A)) != (sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['127', '128'])).
% 0.46/0.68  thf('130', plain, ($false),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['126', '129'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
