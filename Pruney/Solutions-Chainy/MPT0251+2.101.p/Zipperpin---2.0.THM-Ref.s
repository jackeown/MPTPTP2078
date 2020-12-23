%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sWXTCZMIBg

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:15 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 182 expanded)
%              Number of leaves         :   30 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          :  629 (1265 expanded)
%              Number of equality atoms :   68 ( 131 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( r1_xboole_0 @ X23 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X60 @ X61 ) )
      = ( k2_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) )
      = X14 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X60 @ X61 ) )
      = ( k2_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('23',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('24',plain,(
    ! [X57: $i,X59: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X57 ) @ X59 )
      | ~ ( r2_hidden @ X57 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ sk_B_1 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('36',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','38'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B_1 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('46',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('49',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B_1
    = ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('53',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('54',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X60 @ X61 ) )
      = ( k2_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_B_1
    = ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['51','58'])).

thf('60',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X60 @ X61 ) )
      = ( k2_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('62',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sWXTCZMIBg
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 274 iterations in 0.079s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.35/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.35/0.53  thf('0', plain, (![X23 : $i]: (r1_xboole_0 @ X23 @ k1_xboole_0)),
% 0.35/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.35/0.53  thf(t7_xboole_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.53  thf(t4_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.35/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.35/0.53          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.35/0.53  thf(t100_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X10 @ X11)
% 0.35/0.53           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.35/0.53  thf(t21_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X14 : $i, X15 : $i]:
% 0.35/0.53         ((k3_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (X14))),
% 0.35/0.53      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.35/0.53  thf(l51_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X60 : $i, X61 : $i]:
% 0.35/0.53         ((k3_tarski @ (k2_tarski @ X60 @ X61)) = (k2_xboole_0 @ X60 @ X61))),
% 0.35/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X14 : $i, X15 : $i]:
% 0.35/0.53         ((k3_xboole_0 @ X14 @ (k3_tarski @ (k2_tarski @ X14 @ X15))) = (X14))),
% 0.35/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.35/0.53  thf(t17_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.35/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.35/0.53  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.35/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf(t28_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i]:
% 0.35/0.53         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.35/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.53  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X10 @ X11)
% 0.35/0.53           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.35/0.53  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.35/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf(l32_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X7 : $i, X9 : $i]:
% 0.35/0.53         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.35/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.35/0.53  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('19', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.35/0.53  thf(t98_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X27 : $i, X28 : $i]:
% 0.35/0.53         ((k2_xboole_0 @ X27 @ X28)
% 0.35/0.53           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (![X60 : $i, X61 : $i]:
% 0.35/0.53         ((k3_tarski @ (k2_tarski @ X60 @ X61)) = (k2_xboole_0 @ X60 @ X61))),
% 0.35/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X27 : $i, X28 : $i]:
% 0.35/0.53         ((k3_tarski @ (k2_tarski @ X27 @ X28))
% 0.35/0.53           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.35/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.35/0.53  thf(t46_zfmisc_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.35/0.53       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i]:
% 0.35/0.53        ( ( r2_hidden @ A @ B ) =>
% 0.35/0.53          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.35/0.53  thf('23', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(l1_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X57 : $i, X59 : $i]:
% 0.35/0.53         ((r1_tarski @ (k1_tarski @ X57) @ X59) | ~ (r2_hidden @ X57 @ X59))),
% 0.35/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.35/0.53  thf('25', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.35/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i]:
% 0.35/0.53         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.35/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X10 @ X11)
% 0.35/0.53           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.35/0.53         = (k5_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.35/0.53  thf(t91_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.35/0.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 0.35/0.53           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ X0)
% 0.35/0.53           = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.35/0.53           (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))
% 0.35/0.53           = (k5_xboole_0 @ sk_B_1 @ 
% 0.35/0.53              (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ X0))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['22', '33'])).
% 0.35/0.53  thf('35', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      (((k1_xboole_0)
% 0.35/0.53         = (k5_xboole_0 @ sk_B_1 @ 
% 0.35/0.53            (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 0.35/0.53           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.35/0.53           = (k5_xboole_0 @ sk_B_1 @ 
% 0.35/0.53              (k5_xboole_0 @ 
% 0.35/0.53               (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1)) @ X0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.35/0.53         (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.35/0.53         = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['19', '38'])).
% 0.35/0.53  thf(t5_boole, axiom,
% 0.35/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.53  thf('40', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.35/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.35/0.53         (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1))) = (sk_B_1))),
% 0.35/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 0.35/0.53           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.35/0.53  thf('43', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ sk_B_1 @ X0)
% 0.35/0.53           = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.35/0.53              (k5_xboole_0 @ 
% 0.35/0.53               (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1)) @ X0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      (((k5_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.35/0.53         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.35/0.53            (k4_xboole_0 @ 
% 0.35/0.53             (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1)) @ 
% 0.35/0.53             k1_xboole_0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['6', '43'])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      (![X27 : $i, X28 : $i]:
% 0.35/0.53         ((k3_tarski @ (k2_tarski @ X27 @ X28))
% 0.35/0.53           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.35/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.35/0.53  thf('47', plain,
% 0.35/0.53      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.35/0.53         = (k3_tarski @ 
% 0.35/0.53            (k2_tarski @ k1_xboole_0 @ 
% 0.35/0.53             (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1)))))),
% 0.35/0.53      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.35/0.53  thf('48', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.35/0.53  thf('49', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.35/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.35/0.53  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['48', '49'])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      (((sk_B_1)
% 0.35/0.53         = (k3_tarski @ 
% 0.35/0.53            (k2_tarski @ k1_xboole_0 @ 
% 0.35/0.53             (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1)))))),
% 0.35/0.53      inference('demod', [status(thm)], ['47', '50'])).
% 0.35/0.53  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['48', '49'])).
% 0.35/0.53  thf(t51_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.35/0.53       ( A ) ))).
% 0.35/0.53  thf('53', plain,
% 0.35/0.53      (![X20 : $i, X21 : $i]:
% 0.35/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.35/0.53           = (X20))),
% 0.35/0.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.35/0.53  thf('54', plain,
% 0.35/0.53      (![X60 : $i, X61 : $i]:
% 0.35/0.53         ((k3_tarski @ (k2_tarski @ X60 @ X61)) = (k2_xboole_0 @ X60 @ X61))),
% 0.35/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.35/0.53  thf('55', plain,
% 0.35/0.53      (![X20 : $i, X21 : $i]:
% 0.35/0.53         ((k3_tarski @ 
% 0.35/0.53           (k2_tarski @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21)))
% 0.35/0.53           = (X20))),
% 0.35/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.35/0.53  thf('56', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k3_tarski @ (k2_tarski @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))
% 0.35/0.53           = (X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['52', '55'])).
% 0.35/0.53  thf('57', plain,
% 0.35/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.35/0.53  thf('58', plain,
% 0.35/0.53      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['56', '57'])).
% 0.35/0.53  thf('59', plain,
% 0.35/0.53      (((sk_B_1) = (k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.35/0.53      inference('demod', [status(thm)], ['51', '58'])).
% 0.35/0.53  thf('60', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('61', plain,
% 0.35/0.53      (![X60 : $i, X61 : $i]:
% 0.35/0.53         ((k3_tarski @ (k2_tarski @ X60 @ X61)) = (k2_xboole_0 @ X60 @ X61))),
% 0.35/0.53      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.35/0.53  thf('62', plain,
% 0.35/0.53      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_B_1)) != (sk_B_1))),
% 0.35/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.35/0.53  thf('63', plain, ($false),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['59', '62'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.41/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
