%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lH1S8qtwIk

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:56 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 449 expanded)
%              Number of leaves         :   27 ( 156 expanded)
%              Depth                    :   17
%              Number of atoms          : 1011 (3451 expanded)
%              Number of equality atoms :  107 ( 351 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X33: $i,X35: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X33 ) @ X35 )
      | ~ ( r2_hidden @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('51',plain,(
    ! [X38: $i] :
      ( r1_tarski @ X38 @ ( k1_zfmisc_1 @ ( k3_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X38: $i] :
      ( r1_tarski @ X38 @ ( k1_zfmisc_1 @ ( k3_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('57',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['50','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('77',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('86',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('92',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','92'])).

thf('94',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['74','93'])).

thf('95',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','72'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('100',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('102',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','100','101'])).

thf('103',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lH1S8qtwIk
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 325 iterations in 0.137s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.59  thf(t94_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k2_xboole_0 @ A @ B ) =
% 0.38/0.59       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.59           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.38/0.59              (k3_xboole_0 @ X21 @ X22)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.38/0.59  thf(t91_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.59       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.38/0.59  thf('1', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.38/0.59           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.59           = (k5_xboole_0 @ X21 @ 
% 0.38/0.59              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.38/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.59  thf(t140_zfmisc_1, conjecture,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.59       ( ( k2_xboole_0 @
% 0.38/0.59           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.38/0.59         ( B ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i]:
% 0.38/0.59        ( ( r2_hidden @ A @ B ) =>
% 0.38/0.59          ( ( k2_xboole_0 @
% 0.38/0.59              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.38/0.59            ( B ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.38/0.59  thf('3', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(l1_zfmisc_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X33 : $i, X35 : $i]:
% 0.38/0.59         ((r1_tarski @ (k1_tarski @ X33) @ X35) | ~ (r2_hidden @ X33 @ X35))),
% 0.38/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.59  thf('5', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf(t28_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X7 : $i, X8 : $i]:
% 0.38/0.59         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.38/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.59  thf('9', plain,
% 0.38/0.59      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf(t100_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (![X5 : $i, X6 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.38/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('11', plain,
% 0.38/0.59      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.38/0.59         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.38/0.59           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.38/0.59           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.59           = (k5_xboole_0 @ X21 @ 
% 0.38/0.59              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.38/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.38/0.59         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59            (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['13', '14'])).
% 0.38/0.59  thf('16', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf(l32_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X2 : $i, X4 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.38/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.59  thf(t39_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.38/0.59           = (k2_xboole_0 @ X10 @ X11))),
% 0.38/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.38/0.59         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.38/0.59         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59            (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.38/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.59  thf('23', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.38/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      (![X7 : $i, X8 : $i]:
% 0.38/0.59         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.38/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['25', '26'])).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.59           = (k5_xboole_0 @ X21 @ 
% 0.38/0.59              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.38/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.59  thf('29', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.38/0.59           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.59  thf(t5_boole, axiom,
% 0.38/0.59    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.59  thf('30', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.38/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.59  thf('32', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.38/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.59  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.59  thf('34', plain,
% 0.38/0.59      (((sk_B)
% 0.38/0.59         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59            (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['22', '33'])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.38/0.59           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ sk_B @ X0)
% 0.38/0.59           = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.38/0.59  thf('37', plain,
% 0.38/0.59      (((k5_xboole_0 @ sk_B @ 
% 0.38/0.59         (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59          (k1_tarski @ sk_A)))
% 0.38/0.59         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59            (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['2', '36'])).
% 0.38/0.59  thf('38', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      (((k5_xboole_0 @ sk_B @ 
% 0.38/0.59         (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.59          (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.38/0.59         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59            (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (![X5 : $i, X6 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.38/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (![X5 : $i, X6 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.38/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.38/0.59           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59           (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.38/0.59           = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.38/0.59  thf('45', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59           (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.38/0.59           = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['41', '44'])).
% 0.38/0.59  thf('46', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59         (k1_tarski @ sk_A))
% 0.38/0.59         = (k5_xboole_0 @ sk_B @ 
% 0.38/0.59            (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.59             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['40', '45'])).
% 0.38/0.59  thf(t79_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.38/0.59  thf('47', plain,
% 0.38/0.59      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.38/0.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.38/0.59  thf(t83_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (![X15 : $i, X16 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.38/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.38/0.59  thf('49', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.38/0.59           = (k4_xboole_0 @ X1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('50', plain,
% 0.38/0.59      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.38/0.59         = (k5_xboole_0 @ sk_B @ 
% 0.38/0.59            (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.59             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.38/0.59      inference('demod', [status(thm)], ['46', '49'])).
% 0.38/0.59  thf(t100_zfmisc_1, axiom,
% 0.38/0.59    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.38/0.59  thf('51', plain,
% 0.38/0.59      (![X38 : $i]: (r1_tarski @ X38 @ (k1_zfmisc_1 @ (k3_tarski @ X38)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.38/0.59  thf('52', plain,
% 0.38/0.59      (![X7 : $i, X8 : $i]:
% 0.38/0.59         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.38/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.59  thf('53', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k3_xboole_0 @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0))) = (X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.59  thf('54', plain,
% 0.38/0.59      (![X5 : $i, X6 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.38/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('55', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 0.38/0.59           = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['53', '54'])).
% 0.38/0.59  thf('56', plain,
% 0.38/0.59      (![X38 : $i]: (r1_tarski @ X38 @ (k1_zfmisc_1 @ (k3_tarski @ X38)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.38/0.59  thf('57', plain,
% 0.38/0.59      (![X2 : $i, X4 : $i]:
% 0.38/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.38/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.59  thf('58', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0))) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.59  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['55', '58'])).
% 0.38/0.59  thf('60', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.38/0.59           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.59  thf('61', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.59           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['59', '60'])).
% 0.38/0.59  thf('62', plain,
% 0.38/0.59      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.59  thf('63', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X21 @ X22)
% 0.38/0.59           = (k5_xboole_0 @ X21 @ 
% 0.38/0.59              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.38/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.59  thf('64', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.59           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['62', '63'])).
% 0.38/0.59  thf('65', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.38/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.59  thf('66', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['64', '65'])).
% 0.38/0.59  thf('67', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.59           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['61', '66'])).
% 0.38/0.59  thf('68', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['55', '58'])).
% 0.38/0.59  thf('69', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.59           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['61', '66'])).
% 0.38/0.59  thf('70', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['68', '69'])).
% 0.38/0.59  thf('71', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.38/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.59  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['70', '71'])).
% 0.38/0.59  thf('73', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['67', '72'])).
% 0.38/0.59  thf('74', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.59         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.38/0.59         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['50', '73'])).
% 0.38/0.59  thf('75', plain,
% 0.38/0.59      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.38/0.59         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf('76', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.59           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['61', '66'])).
% 0.38/0.59  thf('77', plain,
% 0.38/0.59      (((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.38/0.59         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.38/0.59      inference('sup+', [status(thm)], ['75', '76'])).
% 0.38/0.59  thf('78', plain,
% 0.38/0.59      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.59  thf('79', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.59  thf('80', plain,
% 0.38/0.59      (![X5 : $i, X6 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.38/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('81', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['79', '80'])).
% 0.38/0.59  thf('82', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.38/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['78', '81'])).
% 0.38/0.59  thf('83', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.59  thf('84', plain,
% 0.38/0.59      (((k1_xboole_0) = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['82', '83'])).
% 0.38/0.59  thf('85', plain,
% 0.38/0.59      (((k1_xboole_0) = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['82', '83'])).
% 0.38/0.59  thf('86', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.38/0.59           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.59  thf('87', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.59           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.59              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['85', '86'])).
% 0.38/0.59  thf('88', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['64', '65'])).
% 0.38/0.59  thf('89', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.59           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.59              (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['87', '88'])).
% 0.38/0.59  thf('90', plain,
% 0.38/0.59      (((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.38/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['84', '89'])).
% 0.38/0.59  thf('91', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.38/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.59  thf('92', plain,
% 0.38/0.59      (((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['90', '91'])).
% 0.38/0.59  thf('93', plain,
% 0.38/0.59      (((k1_tarski @ sk_A)
% 0.38/0.59         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.38/0.59      inference('demod', [status(thm)], ['77', '92'])).
% 0.38/0.59  thf('94', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.59         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_tarski @ sk_A))),
% 0.38/0.59      inference('demod', [status(thm)], ['74', '93'])).
% 0.38/0.59  thf('95', plain,
% 0.38/0.59      (![X5 : $i, X6 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X5 @ X6)
% 0.38/0.59           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('96', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.59      inference('demod', [status(thm)], ['67', '72'])).
% 0.38/0.59  thf('97', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         ((k3_xboole_0 @ X1 @ X0)
% 0.38/0.59           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['95', '96'])).
% 0.38/0.59  thf('98', plain,
% 0.38/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.59         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.38/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['94', '97'])).
% 0.38/0.59  thf('99', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['55', '58'])).
% 0.38/0.59  thf('100', plain,
% 0.38/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.38/0.59         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_xboole_0))),
% 0.38/0.59      inference('demod', [status(thm)], ['98', '99'])).
% 0.38/0.59  thf('101', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.38/0.59      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.59  thf('102', plain,
% 0.38/0.59      (((sk_B)
% 0.38/0.59         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59            (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['39', '100', '101'])).
% 0.38/0.59  thf('103', plain,
% 0.38/0.59      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.38/0.59         (k1_tarski @ sk_A)) != (sk_B))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('104', plain, ($false),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
