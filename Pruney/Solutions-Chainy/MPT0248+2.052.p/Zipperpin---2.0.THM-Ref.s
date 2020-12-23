%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c5p2D824Xx

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:25 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 757 expanded)
%              Number of leaves         :   26 ( 243 expanded)
%              Depth                    :   38
%              Number of atoms          : 1418 (6856 expanded)
%              Number of equality atoms :  241 (1186 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','46'])).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('53',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('54',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48
        = ( k1_tarski @ X47 ) )
      | ( X48 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('57',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( ( k3_tarski @ sk_B )
      = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf('65',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('66',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('69',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('72',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','72'])).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('75',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','75'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('81',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('83',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('85',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','72'])).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('87',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('91',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('94',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','94'])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('104',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','104'])).

thf('106',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('108',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('110',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('112',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('114',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('116',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('118',plain,
    ( ( k1_xboole_0
      = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_C @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','118'])).

thf('120',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('121',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('124',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48
        = ( k1_tarski @ X47 ) )
      | ( X48 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['128'])).

thf('130',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['128'])).

thf('131',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['131'])).

thf('133',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('134',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['134'])).

thf('136',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','135'])).

thf('137',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['128'])).

thf('139',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['130','132','140'])).

thf('142',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['129','141'])).

thf('143',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['134'])).

thf('144',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('147',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['145','152'])).

thf('154',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['144','153'])).

thf('155',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['129','141'])).

thf('156',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['134'])).

thf('158',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['156','157'])).

thf('159',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['143','158'])).

thf('160',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['127','142','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','160'])).

thf('162',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['163','166'])).

thf('168',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['129','141'])).

thf('169',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['167','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c5p2D824Xx
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:12:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 754 iterations in 0.280s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.54/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(commutativity_k5_xboole_0, axiom,
% 0.54/0.74    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.54/0.74  thf('0', plain,
% 0.54/0.74      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.54/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.74  thf(t5_boole, axiom,
% 0.54/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.74  thf('1', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.54/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.74  thf('2', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.74  thf(t94_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( k2_xboole_0 @ A @ B ) =
% 0.54/0.74       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      (![X17 : $i, X18 : $i]:
% 0.54/0.74         ((k2_xboole_0 @ X17 @ X18)
% 0.54/0.74           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.54/0.74              (k3_xboole_0 @ X17 @ X18)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.54/0.74  thf(t91_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.74       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.54/0.74  thf('4', plain,
% 0.54/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.54/0.74           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.74  thf('5', plain,
% 0.54/0.74      (![X17 : $i, X18 : $i]:
% 0.54/0.74         ((k2_xboole_0 @ X17 @ X18)
% 0.54/0.74           = (k5_xboole_0 @ X17 @ 
% 0.54/0.74              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.54/0.74      inference('demod', [status(thm)], ['3', '4'])).
% 0.54/0.74  thf('6', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.54/0.74           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['2', '5'])).
% 0.54/0.74  thf('7', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.74      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.74  thf(t100_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.74  thf('8', plain,
% 0.54/0.74      (![X7 : $i, X8 : $i]:
% 0.54/0.74         ((k4_xboole_0 @ X7 @ X8)
% 0.54/0.74           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['7', '8'])).
% 0.54/0.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.75  thf('10', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.75  thf(l32_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.75  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['6', '15'])).
% 0.54/0.75  thf('17', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.75  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X17 : $i, X18 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X17 @ X18)
% 0.54/0.75           = (k5_xboole_0 @ X17 @ 
% 0.54/0.75              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.54/0.75      inference('demod', [status(thm)], ['3', '4'])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['19', '20'])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X7 @ X8)
% 0.54/0.75           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.75  thf(t92_xboole_1, axiom,
% 0.54/0.75    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.75  thf('24', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.75         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.54/0.75           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.75           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['24', '25'])).
% 0.54/0.75  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['26', '27'])).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['23', '28'])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['18', '29'])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X7 @ X8)
% 0.54/0.75           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['26', '27'])).
% 0.54/0.75  thf('34', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k3_xboole_0 @ X1 @ X0)
% 0.54/0.75           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf(t7_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.54/0.75  thf('37', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.54/0.75      inference('sup+', [status(thm)], ['35', '36'])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.75  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.75  thf('40', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.75  thf('41', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.54/0.75      inference('sup+', [status(thm)], ['39', '40'])).
% 0.54/0.75  thf('42', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['34', '41'])).
% 0.54/0.75  thf('43', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf('44', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X7 @ X8)
% 0.54/0.75           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('45', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['43', '44'])).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['42', '45'])).
% 0.54/0.75  thf('47', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['30', '31', '46'])).
% 0.54/0.75  thf(t43_zfmisc_1, conjecture,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.54/0.75          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.54/0.75          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.54/0.75          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.75        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.54/0.75             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.54/0.75             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.54/0.75             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.54/0.75  thf('48', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('49', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['23', '28'])).
% 0.54/0.75  thf('50', plain,
% 0.54/0.75      (((k4_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('51', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('52', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.54/0.75  thf('53', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.54/0.75      inference('sup+', [status(thm)], ['51', '52'])).
% 0.54/0.75  thf(l3_zfmisc_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.54/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (![X47 : $i, X48 : $i]:
% 0.54/0.75         (((X48) = (k1_tarski @ X47))
% 0.54/0.75          | ((X48) = (k1_xboole_0))
% 0.54/0.75          | ~ (r1_tarski @ X48 @ (k1_tarski @ X47)))),
% 0.54/0.75      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.54/0.75  thf('55', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('56', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf(t69_enumset1, axiom,
% 0.54/0.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.75  thf('57', plain,
% 0.54/0.75      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.54/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.75  thf(l51_zfmisc_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.54/0.75  thf('58', plain,
% 0.54/0.75      (![X50 : $i, X51 : $i]:
% 0.54/0.75         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.54/0.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.54/0.75  thf('59', plain,
% 0.54/0.75      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['57', '58'])).
% 0.54/0.75  thf('60', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.75  thf('61', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.54/0.75      inference('sup+', [status(thm)], ['39', '40'])).
% 0.54/0.75  thf('62', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['60', '61'])).
% 0.54/0.75  thf('63', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['59', '62'])).
% 0.54/0.75  thf('64', plain,
% 0.54/0.75      ((((k3_tarski @ sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['56', '63'])).
% 0.54/0.75  thf('65', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.54/0.75      inference('sup+', [status(thm)], ['51', '52'])).
% 0.54/0.75  thf('66', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.75  thf('67', plain,
% 0.54/0.75      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['65', '66'])).
% 0.54/0.75  thf('68', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.75  thf('69', plain,
% 0.54/0.75      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.54/0.75         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['67', '68'])).
% 0.54/0.75  thf('70', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.75  thf('72', plain,
% 0.54/0.75      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.54/0.75  thf('73', plain,
% 0.54/0.75      ((((k2_xboole_0 @ (k1_tarski @ (k3_tarski @ sk_B)) @ sk_B)
% 0.54/0.75          = (k1_tarski @ sk_A))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['64', '72'])).
% 0.54/0.75  thf('74', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.54/0.75  thf('75', plain,
% 0.54/0.75      (((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B)) @ (k1_tarski @ sk_A))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['73', '74'])).
% 0.54/0.75  thf('76', plain,
% 0.54/0.75      (((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B)) @ sk_B)
% 0.54/0.75        | ((sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['55', '75'])).
% 0.54/0.75  thf('77', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0))
% 0.54/0.75        | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B)) @ sk_B))),
% 0.54/0.75      inference('simplify', [status(thm)], ['76'])).
% 0.54/0.75  thf('78', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.75  thf('79', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((k4_xboole_0 @ (k1_tarski @ (k3_tarski @ sk_B)) @ sk_B)
% 0.54/0.75            = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['77', '78'])).
% 0.54/0.75  thf('80', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.75  thf('81', plain,
% 0.54/0.75      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ (k3_tarski @ sk_B)))
% 0.54/0.75          = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['79', '80'])).
% 0.54/0.75  thf('82', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.75  thf('83', plain,
% 0.54/0.75      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ (k3_tarski @ sk_B))) = (sk_B))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['81', '82'])).
% 0.54/0.75  thf('84', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('85', plain,
% 0.54/0.75      ((((k2_xboole_0 @ (k1_tarski @ (k3_tarski @ sk_B)) @ sk_B)
% 0.54/0.75          = (k1_tarski @ sk_A))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['64', '72'])).
% 0.54/0.75  thf('86', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.54/0.75  thf('87', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.75  thf('88', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['86', '87'])).
% 0.54/0.75  thf('89', plain,
% 0.54/0.75      ((((k4_xboole_0 @ (k1_tarski @ (k3_tarski @ sk_B)) @ (k1_tarski @ sk_A))
% 0.54/0.75          = (k1_xboole_0))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['85', '88'])).
% 0.54/0.75  thf('90', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.75  thf('91', plain,
% 0.54/0.75      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k3_tarski @ sk_B)))
% 0.54/0.75          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['89', '90'])).
% 0.54/0.75  thf('92', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf('93', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.75  thf('94', plain,
% 0.54/0.75      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ (k3_tarski @ sk_B)))
% 0.54/0.75          = (k1_tarski @ sk_A))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.54/0.75  thf('95', plain,
% 0.54/0.75      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ (k3_tarski @ sk_B)))
% 0.54/0.75          = (k1_tarski @ sk_A))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['84', '94'])).
% 0.54/0.75  thf('96', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((k2_xboole_0 @ sk_B @ (k1_tarski @ (k3_tarski @ sk_B)))
% 0.54/0.75            = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['95'])).
% 0.54/0.75  thf('97', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['86', '87'])).
% 0.54/0.75  thf('98', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.75  thf('99', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.54/0.75           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['97', '98'])).
% 0.54/0.75  thf('100', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.75  thf('101', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.54/0.75           = (k2_xboole_0 @ X1 @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['99', '100'])).
% 0.54/0.75  thf('102', plain,
% 0.54/0.75      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.54/0.75          = (k2_xboole_0 @ sk_B @ (k1_tarski @ (k3_tarski @ sk_B))))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['96', '101'])).
% 0.54/0.75  thf('103', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.54/0.75  thf('104', plain,
% 0.54/0.75      (((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.54/0.75         (k2_xboole_0 @ sk_B @ (k1_tarski @ (k3_tarski @ sk_B))))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['102', '103'])).
% 0.54/0.75  thf('105', plain,
% 0.54/0.75      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 0.54/0.75        | ((sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['83', '104'])).
% 0.54/0.75  thf('106', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 0.54/0.75      inference('simplify', [status(thm)], ['105'])).
% 0.54/0.75  thf('107', plain,
% 0.54/0.75      (![X4 : $i, X6 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.54/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.75  thf('108', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['106', '107'])).
% 0.54/0.75  thf('109', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k3_xboole_0 @ X1 @ X0)
% 0.54/0.75           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('110', plain,
% 0.54/0.75      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.54/0.75          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['108', '109'])).
% 0.54/0.75  thf('111', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.75  thf('112', plain,
% 0.54/0.75      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.75  thf('113', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.75  thf('114', plain,
% 0.54/0.75      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.54/0.75  thf('115', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X7 @ X8)
% 0.54/0.75           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.75  thf('116', plain,
% 0.54/0.75      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.54/0.75          = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['114', '115'])).
% 0.54/0.75  thf('117', plain,
% 0.54/0.75      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['65', '66'])).
% 0.54/0.75  thf('118', plain,
% 0.54/0.75      ((((k1_xboole_0) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('demod', [status(thm)], ['116', '117'])).
% 0.54/0.75  thf('119', plain,
% 0.54/0.75      ((((k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_B))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['50', '118'])).
% 0.54/0.75  thf('120', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i]:
% 0.54/0.75         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.75  thf('121', plain,
% 0.54/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0))
% 0.54/0.75        | (r1_tarski @ sk_C @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['119', '120'])).
% 0.54/0.75  thf('122', plain, (((r1_tarski @ sk_C @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['121'])).
% 0.54/0.75  thf('123', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('124', plain,
% 0.54/0.75      (![X47 : $i, X48 : $i]:
% 0.54/0.75         (((X48) = (k1_tarski @ X47))
% 0.54/0.75          | ((X48) = (k1_xboole_0))
% 0.54/0.75          | ~ (r1_tarski @ X48 @ (k1_tarski @ X47)))),
% 0.54/0.75      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.54/0.75  thf('125', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (r1_tarski @ X0 @ sk_B)
% 0.54/0.75          | ((sk_B) = (k1_xboole_0))
% 0.54/0.75          | ((X0) = (k1_xboole_0))
% 0.54/0.75          | ((X0) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['123', '124'])).
% 0.54/0.75  thf('126', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0))
% 0.54/0.75        | ((sk_C) = (k1_tarski @ sk_A))
% 0.54/0.75        | ((sk_C) = (k1_xboole_0))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['122', '125'])).
% 0.54/0.75  thf('127', plain,
% 0.54/0.75      ((((sk_C) = (k1_xboole_0))
% 0.54/0.75        | ((sk_C) = (k1_tarski @ sk_A))
% 0.54/0.75        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['126'])).
% 0.54/0.75  thf('128', plain,
% 0.54/0.75      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('129', plain,
% 0.54/0.75      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.54/0.75      inference('split', [status(esa)], ['128'])).
% 0.54/0.75  thf('130', plain,
% 0.54/0.75      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.54/0.75      inference('split', [status(esa)], ['128'])).
% 0.54/0.75  thf('131', plain,
% 0.54/0.75      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('132', plain,
% 0.54/0.75      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('split', [status(esa)], ['131'])).
% 0.54/0.75  thf('133', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['53', '54'])).
% 0.54/0.75  thf('134', plain,
% 0.54/0.75      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('135', plain,
% 0.54/0.75      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.54/0.75      inference('split', [status(esa)], ['134'])).
% 0.54/0.75  thf('136', plain,
% 0.54/0.75      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.54/0.75         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['133', '135'])).
% 0.54/0.75  thf('137', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['136'])).
% 0.54/0.75  thf('138', plain,
% 0.54/0.75      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['128'])).
% 0.54/0.75  thf('139', plain,
% 0.54/0.75      ((((sk_B) != (sk_B)))
% 0.54/0.75         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['137', '138'])).
% 0.54/0.75  thf('140', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['139'])).
% 0.54/0.75  thf('141', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sat_resolution*', [status(thm)], ['130', '132', '140'])).
% 0.54/0.75  thf('142', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['129', '141'])).
% 0.54/0.75  thf('143', plain,
% 0.54/0.75      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['134'])).
% 0.54/0.75  thf('144', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('145', plain,
% 0.54/0.75      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['136'])).
% 0.54/0.75  thf('146', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['0', '1'])).
% 0.54/0.75  thf('147', plain,
% 0.54/0.75      (![X17 : $i, X18 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ X17 @ X18)
% 0.54/0.75           = (k5_xboole_0 @ X17 @ 
% 0.54/0.75              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.54/0.75      inference('demod', [status(thm)], ['3', '4'])).
% 0.54/0.75  thf('148', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['146', '147'])).
% 0.54/0.75  thf('149', plain,
% 0.54/0.75      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['9', '12'])).
% 0.54/0.75  thf('150', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['148', '149'])).
% 0.54/0.75  thf('151', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.75  thf('152', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['150', '151'])).
% 0.54/0.75  thf('153', plain,
% 0.54/0.75      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.54/0.75         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['145', '152'])).
% 0.54/0.75  thf('154', plain,
% 0.54/0.75      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['144', '153'])).
% 0.54/0.75  thf('155', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['129', '141'])).
% 0.54/0.75  thf('156', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['154', '155'])).
% 0.54/0.75  thf('157', plain,
% 0.54/0.75      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('split', [status(esa)], ['134'])).
% 0.54/0.75  thf('158', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.54/0.75      inference('sat_resolution*', [status(thm)], ['156', '157'])).
% 0.54/0.75  thf('159', plain, (((sk_C) != (k1_xboole_0))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['143', '158'])).
% 0.54/0.75  thf('160', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['127', '142', '159'])).
% 0.54/0.75  thf('161', plain, (![X0 : $i]: ((sk_B) = (k4_xboole_0 @ X0 @ X0))),
% 0.54/0.75      inference('demod', [status(thm)], ['47', '160'])).
% 0.54/0.75  thf('162', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('163', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k1_tarski @ sk_A) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_C))),
% 0.54/0.75      inference('sup+', [status(thm)], ['161', '162'])).
% 0.54/0.75  thf('164', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['37', '38'])).
% 0.54/0.75  thf('165', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['150', '151'])).
% 0.54/0.75  thf('166', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.54/0.75      inference('sup+', [status(thm)], ['164', '165'])).
% 0.54/0.75  thf('167', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['163', '166'])).
% 0.54/0.75  thf('168', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['129', '141'])).
% 0.54/0.75  thf('169', plain, ($false),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['167', '168'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
