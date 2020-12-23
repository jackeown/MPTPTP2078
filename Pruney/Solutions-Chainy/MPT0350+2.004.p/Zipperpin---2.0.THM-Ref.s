%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rQP9SkqbnX

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:45 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 617 expanded)
%              Number of leaves         :   38 ( 217 expanded)
%              Depth                    :   13
%              Number of atoms          : 1195 (4600 expanded)
%              Number of equality atoms :  135 ( 562 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k3_subset_1 @ X40 @ X41 )
        = ( k4_xboole_0 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','16','19','20'])).

thf('22',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','29','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('58',plain,
    ( ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('61',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ X37 )
      | ( r2_hidden @ X36 @ X37 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('63',plain,(
    ! [X44: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('64',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('65',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ( r1_tarski @ X32 @ X30 )
      | ( X31
       != ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('66',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X32 @ X30 )
      | ~ ( r2_hidden @ X32 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['64','66'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('71',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('74',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('76',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('79',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','80'])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['67','68'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('88',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['67','68'])).

thf('89',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('94',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['87','92','93'])).

thf('95',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','86','94'])).

thf('96',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('98',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('105',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('113',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['103','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('116',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','95','114','115'])).

thf('117',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('118',plain,(
    ! [X39: $i] :
      ( ( k2_subset_1 @ X39 )
      = X39 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('119',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('121',plain,(
    ! [X42: $i,X43: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('122',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('124',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k4_subset_1 @ X46 @ X45 @ X47 )
        = ( k2_xboole_0 @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['119','126'])).

thf('128',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['116','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rQP9SkqbnX
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 478 iterations in 0.173s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.63  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(t25_subset_1, conjecture,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.46/0.63         ( k2_subset_1 @ A ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i]:
% 0.46/0.63        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.46/0.63            ( k2_subset_1 @ A ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.46/0.63  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d5_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X40 : $i, X41 : $i]:
% 0.46/0.63         (((k3_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))
% 0.46/0.63          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.63  thf(t100_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X5 : $i, X6 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.63           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.63  thf(t112_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.46/0.63       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.46/0.63           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.46/0.63           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.46/0.63           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['3', '6'])).
% 0.46/0.63  thf(t22_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.46/0.63  thf(commutativity_k2_tarski, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X22 : $i, X23 : $i]:
% 0.46/0.63         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 0.46/0.63      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.63  thf(l51_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X34 : $i, X35 : $i]:
% 0.46/0.63         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 0.46/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X34 : $i, X35 : $i]:
% 0.46/0.63         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 0.46/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf(t46_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['8', '15'])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (![X5 : $i, X6 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.63           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['7', '16', '19', '20'])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['2', '21'])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.46/0.63         = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf(d6_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k5_xboole_0 @ A @ B ) =
% 0.46/0.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X2 @ X3)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X1 @ X0)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X2 @ X3)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.63  thf('30', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.46/0.63  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X2 @ X3)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.63  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.46/0.63      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.46/0.63  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.63  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '37'])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.46/0.63           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k1_xboole_0) = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.63  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '37'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.63  thf(t94_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k2_xboole_0 @ A @ B ) =
% 0.46/0.63       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      (![X20 : $i, X21 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ X20 @ X21)
% 0.46/0.63           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.46/0.63              (k3_xboole_0 @ X20 @ X21)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.63  thf(t91_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.63       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.46/0.63           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      (![X20 : $i, X21 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ X20 @ X21)
% 0.46/0.63           = (k5_xboole_0 @ X20 @ 
% 0.46/0.63              (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X20 @ X21))))),
% 0.46/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.63           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['42', '45'])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      (![X10 : $i, X11 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['48', '49'])).
% 0.46/0.63  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['47', '50'])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('53', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['51', '52'])).
% 0.46/0.63  thf(t5_boole, axiom,
% 0.46/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.63  thf('54', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.63  thf('55', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['46', '53', '54'])).
% 0.46/0.63  thf('56', plain,
% 0.46/0.63      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.46/0.63         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['24', '29', '55'])).
% 0.46/0.63  thf('57', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X2 @ X3)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      (((k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.46/0.63         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.46/0.63            (k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.46/0.63      inference('sup+', [status(thm)], ['56', '57'])).
% 0.46/0.63  thf('59', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf('60', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d2_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.63       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.63         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.63  thf('61', plain,
% 0.46/0.63      (![X36 : $i, X37 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X36 @ X37)
% 0.46/0.63          | (r2_hidden @ X36 @ X37)
% 0.46/0.63          | (v1_xboole_0 @ X37))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.63  thf('62', plain,
% 0.46/0.63      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.63        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.63  thf(fc1_subset_1, axiom,
% 0.46/0.63    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.63  thf('63', plain, (![X44 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X44))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.63  thf('64', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['62', '63'])).
% 0.46/0.63  thf(d1_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X32 @ X31)
% 0.46/0.63          | (r1_tarski @ X32 @ X30)
% 0.46/0.63          | ((X31) != (k1_zfmisc_1 @ X30)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      (![X30 : $i, X32 : $i]:
% 0.46/0.63         ((r1_tarski @ X32 @ X30) | ~ (r2_hidden @ X32 @ (k1_zfmisc_1 @ X30)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['65'])).
% 0.46/0.63  thf('67', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['64', '66'])).
% 0.46/0.63  thf(t28_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i]:
% 0.46/0.63         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.63  thf('69', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('70', plain,
% 0.46/0.63      (![X20 : $i, X21 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ X20 @ X21)
% 0.46/0.63           = (k5_xboole_0 @ X20 @ 
% 0.46/0.63              (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X20 @ X21))))),
% 0.46/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.63  thf('71', plain,
% 0.46/0.63      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.46/0.63         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['69', '70'])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.63  thf('73', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X2 @ X3)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.63  thf('74', plain,
% 0.46/0.63      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.46/0.63         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 0.46/0.63            (k3_subset_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['72', '73'])).
% 0.46/0.63  thf('75', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('76', plain,
% 0.46/0.63      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.46/0.63         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.46/0.63            (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.63  thf('77', plain,
% 0.46/0.63      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.63  thf('78', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X2 @ X3)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.63  thf('79', plain,
% 0.46/0.63      (((k5_xboole_0 @ sk_A @ sk_B)
% 0.46/0.63         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.46/0.63            (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['77', '78'])).
% 0.46/0.63  thf('80', plain,
% 0.46/0.63      (((k5_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['76', '79'])).
% 0.46/0.63  thf('81', plain,
% 0.46/0.63      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.46/0.63         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['71', '80'])).
% 0.46/0.63  thf('82', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('83', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['48', '49'])).
% 0.46/0.63  thf('84', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['82', '83'])).
% 0.46/0.63  thf('85', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('86', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.63  thf('87', plain,
% 0.46/0.63      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.46/0.63         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.46/0.63            (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.63  thf('88', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.63  thf('89', plain,
% 0.46/0.63      (![X5 : $i, X6 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.63           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.63  thf('90', plain,
% 0.46/0.63      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['88', '89'])).
% 0.46/0.63  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '37'])).
% 0.46/0.63  thf('92', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.63  thf('93', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['47', '50'])).
% 0.46/0.63  thf('94', plain,
% 0.46/0.63      (((k5_xboole_0 @ sk_B @ sk_A) = (k3_subset_1 @ sk_A @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['87', '92', '93'])).
% 0.46/0.63  thf('95', plain,
% 0.46/0.63      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['81', '86', '94'])).
% 0.46/0.63  thf('96', plain,
% 0.46/0.63      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['2', '21'])).
% 0.46/0.63  thf('97', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['8', '15'])).
% 0.46/0.63  thf('98', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X2 @ X3)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.63  thf('99', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.46/0.63              k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['97', '98'])).
% 0.46/0.63  thf('100', plain,
% 0.46/0.63      (![X5 : $i, X6 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.63           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.63  thf('101', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['47', '50'])).
% 0.46/0.63  thf('102', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.63           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.63      inference('demod', [status(thm)], ['99', '100', '101'])).
% 0.46/0.63  thf('103', plain,
% 0.46/0.63      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.46/0.63         = (k4_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['96', '102'])).
% 0.46/0.63  thf('104', plain,
% 0.46/0.63      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.63      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.63  thf('105', plain,
% 0.46/0.63      (![X5 : $i, X6 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X5 @ X6)
% 0.46/0.63           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.63  thf('106', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.63           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['104', '105'])).
% 0.46/0.63  thf('107', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['34', '37'])).
% 0.46/0.63  thf('108', plain,
% 0.46/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['106', '107'])).
% 0.46/0.63  thf('109', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X2 @ X3)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.46/0.63  thf('110', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.46/0.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['108', '109'])).
% 0.46/0.63  thf('111', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.63  thf('112', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['47', '50'])).
% 0.46/0.63  thf('113', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.46/0.63  thf('114', plain,
% 0.46/0.63      (((k4_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['103', '113'])).
% 0.46/0.63  thf('115', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.63  thf('116', plain,
% 0.46/0.63      (((sk_A) = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['58', '59', '95', '114', '115'])).
% 0.46/0.63  thf('117', plain,
% 0.46/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.46/0.63         != (k2_subset_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.63  thf('118', plain, (![X39 : $i]: ((k2_subset_1 @ X39) = (X39))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.63  thf('119', plain,
% 0.46/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['117', '118'])).
% 0.46/0.63  thf('120', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_k3_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.63       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.63  thf('121', plain,
% 0.46/0.63      (![X42 : $i, X43 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (k3_subset_1 @ X42 @ X43) @ (k1_zfmisc_1 @ X42))
% 0.46/0.63          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.46/0.63  thf('122', plain,
% 0.46/0.63      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['120', '121'])).
% 0.46/0.63  thf('123', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k4_subset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.63       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.63  thf('124', plain,
% 0.46/0.63      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 0.46/0.63          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46))
% 0.46/0.63          | ((k4_subset_1 @ X46 @ X45 @ X47) = (k2_xboole_0 @ X45 @ X47)))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.46/0.63  thf('125', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['123', '124'])).
% 0.46/0.63  thf('126', plain,
% 0.46/0.63      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.46/0.63         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['122', '125'])).
% 0.46/0.63  thf('127', plain,
% 0.46/0.63      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['119', '126'])).
% 0.46/0.63  thf('128', plain, ($false),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['116', '127'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
