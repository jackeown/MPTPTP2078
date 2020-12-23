%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g0BgKQ4kaU

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:47 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  148 (1843 expanded)
%              Number of leaves         :   35 ( 671 expanded)
%              Depth                    :   21
%              Number of atoms          : 1063 (14306 expanded)
%              Number of equality atoms :  117 (1697 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('40',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','37','38','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
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
    inference('sup+',[status(thm)],['26','27'])).

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

thf('48',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('54',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','53'])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','53'])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('65',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','53'])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('68',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('70',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('73',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('75',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('76',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('78',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('79',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['74','85'])).

thf('87',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','87'])).

thf('89',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('90',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
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

thf('91',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X30 @ X34 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('92',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) )
      | ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('95',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X25 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('100',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['88','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','87'])).

thf('106',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('107',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['104','105','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g0BgKQ4kaU
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.74  % Solved by: fo/fo7.sh
% 0.51/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.74  % done 718 iterations in 0.284s
% 0.51/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.74  % SZS output start Refutation
% 0.51/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.51/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.51/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.51/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.74  thf(t2_boole, axiom,
% 0.51/0.74    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.51/0.74  thf('0', plain,
% 0.51/0.74      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.51/0.74  thf(t100_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.74  thf('1', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X10 @ X11)
% 0.51/0.74           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.74  thf('2', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['0', '1'])).
% 0.51/0.74  thf(t5_boole, axiom,
% 0.51/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.74  thf('3', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.51/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.74  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.51/0.74  thf(t36_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.51/0.74  thf('5', plain,
% 0.51/0.74      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.51/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.51/0.74  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.51/0.74      inference('sup+', [status(thm)], ['4', '5'])).
% 0.51/0.74  thf(t28_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.51/0.74  thf('7', plain,
% 0.51/0.74      (![X12 : $i, X13 : $i]:
% 0.51/0.74         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.51/0.74  thf('8', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.51/0.74  thf('9', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X10 @ X11)
% 0.51/0.74           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.74  thf('10', plain,
% 0.51/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.51/0.74  thf(t92_xboole_1, axiom,
% 0.51/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.51/0.74  thf('11', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.74  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.51/0.74  thf(t49_zfmisc_1, conjecture,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.51/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.74    (~( ![A:$i,B:$i]:
% 0.51/0.74        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.51/0.74    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.51/0.74  thf('13', plain,
% 0.51/0.74      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(t94_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k2_xboole_0 @ A @ B ) =
% 0.51/0.74       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.74  thf('14', plain,
% 0.51/0.74      (![X23 : $i, X24 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X23 @ X24)
% 0.51/0.74           = (k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ 
% 0.51/0.74              (k3_xboole_0 @ X23 @ X24)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.51/0.74  thf(commutativity_k5_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.51/0.74  thf('15', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('16', plain,
% 0.51/0.74      (![X23 : $i, X24 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X23 @ X24)
% 0.51/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ 
% 0.51/0.74              (k5_xboole_0 @ X23 @ X24)))),
% 0.51/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.74  thf('17', plain,
% 0.51/0.74      (![X23 : $i, X24 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X23 @ X24)
% 0.51/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ 
% 0.51/0.74              (k5_xboole_0 @ X23 @ X24)))),
% 0.51/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.74  thf('18', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.51/0.74           = (k5_xboole_0 @ 
% 0.51/0.74              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.51/0.74              (k2_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['16', '17'])).
% 0.51/0.74  thf('19', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('20', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.51/0.74           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.51/0.74              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.51/0.74      inference('demod', [status(thm)], ['18', '19'])).
% 0.51/0.74  thf('21', plain,
% 0.51/0.74      (((k2_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.51/0.74         (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.51/0.74         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.51/0.74            (k3_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.51/0.74             (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.51/0.74      inference('sup+', [status(thm)], ['13', '20'])).
% 0.51/0.74  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.74  thf('22', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('23', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('24', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('25', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('26', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('27', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.51/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.74  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['26', '27'])).
% 0.51/0.74  thf('29', plain,
% 0.51/0.74      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.51/0.74         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.51/0.74         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.51/0.74            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.51/0.74      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '28'])).
% 0.51/0.74  thf('30', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('31', plain,
% 0.51/0.74      (![X23 : $i, X24 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X23 @ X24)
% 0.51/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ 
% 0.51/0.74              (k5_xboole_0 @ X23 @ X24)))),
% 0.51/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.74  thf('32', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X0 @ X1)
% 0.51/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['30', '31'])).
% 0.51/0.74  thf('33', plain,
% 0.51/0.74      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.51/0.74         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.51/0.74         = (k5_xboole_0 @ 
% 0.51/0.74            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.51/0.74             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.51/0.74            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.51/0.74             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.51/0.74      inference('sup+', [status(thm)], ['29', '32'])).
% 0.51/0.74  thf(t91_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.51/0.74       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.51/0.74  thf('34', plain,
% 0.51/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.51/0.74           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.74  thf('35', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('36', plain,
% 0.51/0.74      (![X10 : $i, X11 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X10 @ X11)
% 0.51/0.74           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.74  thf('37', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X0 @ X1)
% 0.51/0.74           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['35', '36'])).
% 0.51/0.74  thf('38', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('39', plain,
% 0.51/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.51/0.74           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.74  thf('40', plain,
% 0.51/0.74      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.51/0.74         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.51/0.74         = (k5_xboole_0 @ sk_B @ 
% 0.51/0.74            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.51/0.74             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.51/0.74              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.51/0.74      inference('demod', [status(thm)], ['33', '34', '37', '38', '39'])).
% 0.51/0.74  thf('41', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('42', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.74  thf('43', plain,
% 0.51/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.51/0.74           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.74  thf('44', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.51/0.74           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['42', '43'])).
% 0.51/0.74  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['26', '27'])).
% 0.51/0.74  thf('46', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('demod', [status(thm)], ['44', '45'])).
% 0.51/0.74  thf('47', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['41', '46'])).
% 0.51/0.74  thf('48', plain,
% 0.51/0.74      (((sk_B)
% 0.51/0.74         = (k5_xboole_0 @ 
% 0.51/0.74            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.51/0.74             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.51/0.74              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.51/0.74            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.51/0.74             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.51/0.74      inference('sup+', [status(thm)], ['40', '47'])).
% 0.51/0.74  thf('49', plain,
% 0.51/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.51/0.74           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.51/0.74  thf('50', plain,
% 0.51/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.51/0.74  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.51/0.74  thf('52', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['26', '27'])).
% 0.51/0.74  thf('54', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.51/0.74      inference('demod', [status(thm)], ['48', '49', '50', '51', '52', '53'])).
% 0.51/0.74  thf('55', plain,
% 0.51/0.74      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.51/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.51/0.74  thf('56', plain,
% 0.51/0.74      (![X12 : $i, X13 : $i]:
% 0.51/0.74         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.51/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.51/0.74  thf('57', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.51/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['55', '56'])).
% 0.51/0.74  thf('58', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('59', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.51/0.74           = (k4_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('demod', [status(thm)], ['57', '58'])).
% 0.51/0.74  thf('60', plain,
% 0.51/0.74      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.51/0.74         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.51/0.74      inference('sup+', [status(thm)], ['54', '59'])).
% 0.51/0.74  thf('61', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf('62', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.51/0.74      inference('demod', [status(thm)], ['48', '49', '50', '51', '52', '53'])).
% 0.51/0.74  thf('63', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.51/0.74      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.51/0.74  thf('64', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((k4_xboole_0 @ X0 @ X1)
% 0.51/0.74           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('sup+', [status(thm)], ['35', '36'])).
% 0.51/0.74  thf('65', plain,
% 0.51/0.74      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.51/0.74         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.51/0.74      inference('sup+', [status(thm)], ['63', '64'])).
% 0.51/0.74  thf('66', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.51/0.74      inference('demod', [status(thm)], ['48', '49', '50', '51', '52', '53'])).
% 0.51/0.74  thf('67', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('68', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.51/0.74      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.51/0.74  thf('69', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.51/0.74      inference('demod', [status(thm)], ['44', '45'])).
% 0.51/0.74  thf('70', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.51/0.74      inference('sup+', [status(thm)], ['68', '69'])).
% 0.51/0.74  thf('71', plain,
% 0.51/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.51/0.74  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.51/0.74  thf('73', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.51/0.74  thf('74', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.51/0.74  thf('75', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 0.51/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.51/0.74  thf('76', plain,
% 0.51/0.74      (![X23 : $i, X24 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X23 @ X24)
% 0.51/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ 
% 0.51/0.74              (k5_xboole_0 @ X23 @ X24)))),
% 0.51/0.74      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.74  thf('77', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k2_xboole_0 @ X0 @ X0)
% 0.51/0.74           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['75', '76'])).
% 0.51/0.74  thf(t69_enumset1, axiom,
% 0.51/0.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.74  thf('78', plain,
% 0.51/0.74      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.51/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.74  thf(l51_zfmisc_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('79', plain,
% 0.51/0.74      (![X65 : $i, X66 : $i]:
% 0.51/0.74         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 0.51/0.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.74  thf('80', plain,
% 0.51/0.74      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['78', '79'])).
% 0.51/0.74  thf('81', plain,
% 0.51/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.51/0.74  thf('82', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['26', '27'])).
% 0.51/0.74  thf('83', plain,
% 0.51/0.74      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('demod', [status(thm)], ['77', '80', '81', '82'])).
% 0.51/0.74  thf('84', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.51/0.74  thf('85', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['83', '84'])).
% 0.51/0.74  thf('86', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.51/0.74      inference('sup+', [status(thm)], ['74', '85'])).
% 0.51/0.74  thf('87', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.51/0.74      inference('demod', [status(thm)], ['73', '86'])).
% 0.51/0.74  thf('88', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k1_tarski @ (k3_tarski @ (k4_xboole_0 @ X0 @ X0))) = (k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['12', '87'])).
% 0.51/0.74  thf('89', plain,
% 0.51/0.74      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.51/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.74  thf(t70_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.51/0.74  thf('90', plain,
% 0.51/0.74      (![X38 : $i, X39 : $i]:
% 0.51/0.74         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.51/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.74  thf(d1_enumset1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.51/0.74       ( ![E:$i]:
% 0.51/0.74         ( ( r2_hidden @ E @ D ) <=>
% 0.51/0.74           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_2, axiom,
% 0.51/0.74    (![E:$i,C:$i,B:$i,A:$i]:
% 0.51/0.74     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.51/0.74       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_3, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.51/0.74       ( ![E:$i]:
% 0.51/0.74         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.51/0.74  thf('91', plain,
% 0.51/0.74      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.51/0.74         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33)
% 0.51/0.74          | (r2_hidden @ X30 @ X34)
% 0.51/0.74          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.74  thf('92', plain,
% 0.51/0.74      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.51/0.74         ((r2_hidden @ X30 @ (k1_enumset1 @ X33 @ X32 @ X31))
% 0.51/0.74          | (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33))),
% 0.51/0.74      inference('simplify', [status(thm)], ['91'])).
% 0.51/0.74  thf('93', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.51/0.74          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['90', '92'])).
% 0.51/0.74  thf('94', plain,
% 0.51/0.74      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.51/0.74         (((X26) != (X25)) | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X25))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.74  thf('95', plain,
% 0.51/0.74      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.51/0.74         ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X25)),
% 0.51/0.74      inference('simplify', [status(thm)], ['94'])).
% 0.51/0.74  thf('96', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['93', '95'])).
% 0.51/0.74  thf('97', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['89', '96'])).
% 0.51/0.74  thf('98', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.51/0.74  thf('99', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.74  thf(t4_xboole_0, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.51/0.74            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.51/0.74  thf('100', plain,
% 0.51/0.74      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.51/0.74          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.51/0.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.51/0.74  thf('101', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.51/0.74          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['99', '100'])).
% 0.51/0.74  thf('102', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['98', '101'])).
% 0.51/0.74  thf('103', plain,
% 0.51/0.74      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['97', '102'])).
% 0.51/0.74  thf('104', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ~ (r1_xboole_0 @ k1_xboole_0 @ 
% 0.51/0.74            (k1_tarski @ (k3_tarski @ (k4_xboole_0 @ X0 @ X0))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['88', '103'])).
% 0.51/0.74  thf('105', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k1_tarski @ (k3_tarski @ (k4_xboole_0 @ X0 @ X0))) = (k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['12', '87'])).
% 0.51/0.74  thf('106', plain,
% 0.51/0.74      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.51/0.74  thf(l97_xboole_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.51/0.74  thf('107', plain,
% 0.51/0.74      (![X8 : $i, X9 : $i]:
% 0.51/0.74         (r1_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9))),
% 0.51/0.74      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.51/0.74  thf('108', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         (r1_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.74      inference('sup+', [status(thm)], ['106', '107'])).
% 0.51/0.74  thf('109', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.51/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.74  thf('110', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.51/0.74      inference('demod', [status(thm)], ['108', '109'])).
% 0.51/0.74  thf('111', plain, ($false),
% 0.51/0.74      inference('demod', [status(thm)], ['104', '105', '110'])).
% 0.51/0.74  
% 0.51/0.74  % SZS output end Refutation
% 0.51/0.74  
% 0.61/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
