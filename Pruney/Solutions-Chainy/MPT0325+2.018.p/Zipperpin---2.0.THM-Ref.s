%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bz5p5ZDU4y

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:42 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 207 expanded)
%              Number of leaves         :   21 (  71 expanded)
%              Depth                    :   24
%              Number of atoms          :  762 (1764 expanded)
%              Number of equality atoms :   91 ( 197 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X21 @ X23 ) @ X22 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
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
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X17 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('8',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ X24 @ ( k4_xboole_0 @ X21 @ X23 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X21 ) @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_B ) @ X0 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_B ) @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['17','18'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k3_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','24','26','37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ X24 @ ( k4_xboole_0 @ X21 @ X23 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X21 ) @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('48',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X21 @ X23 ) @ X22 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('54',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('56',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['51','52','54','55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('61',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['45'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['45'])).

thf('71',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['46','71'])).

thf('73',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['44','72'])).

thf('74',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('75',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','73','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bz5p5ZDU4y
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/1.01  % Solved by: fo/fo7.sh
% 0.77/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/1.01  % done 896 iterations in 0.553s
% 0.77/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/1.01  % SZS output start Refutation
% 0.77/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.77/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.77/1.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/1.01  thf(sk_D_type, type, sk_D: $i).
% 0.77/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.77/1.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.77/1.01  thf(t138_zfmisc_1, conjecture,
% 0.77/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.01     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.77/1.01       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.77/1.01         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.77/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.77/1.01    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.01        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.77/1.01          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.77/1.01            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.77/1.01    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.77/1.01  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(t125_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.77/1.01         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.77/1.01       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.77/1.01         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.77/1.01  thf('1', plain,
% 0.77/1.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ X21 @ X23) @ X22)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X21 @ X22) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X23 @ X22)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('2', plain,
% 0.77/1.01      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf(t28_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.77/1.01  thf('3', plain,
% 0.77/1.01      (![X11 : $i, X12 : $i]:
% 0.77/1.01         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.77/1.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/1.01  thf('4', plain,
% 0.77/1.01      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.77/1.01         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.77/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/1.01  thf('5', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('6', plain,
% 0.77/1.01      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.77/1.01         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['4', '5'])).
% 0.77/1.01  thf(t123_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/1.01     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.77/1.01       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.77/1.01  thf('7', plain,
% 0.77/1.01      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ X17 @ X19) @ (k3_xboole_0 @ X18 @ X20))
% 0.77/1.01           = (k3_xboole_0 @ (k2_zfmisc_1 @ X17 @ X18) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X19 @ X20)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.77/1.01  thf('8', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf('9', plain,
% 0.77/1.01      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ X24 @ (k4_xboole_0 @ X21 @ X23))
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X24 @ X21) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X24 @ X23)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('10', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.77/1.01           (k4_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_B) @ X0))
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.77/1.01              (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['8', '9'])).
% 0.77/1.01  thf('11', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.77/1.01         (k4_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_B) @ sk_B))
% 0.77/1.01         = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 0.77/1.01            sk_B))),
% 0.77/1.01      inference('sup+', [status(thm)], ['1', '10'])).
% 0.77/1.01  thf('12', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf(idempotence_k3_xboole_0, axiom,
% 0.77/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/1.01  thf('13', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/1.01      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.77/1.01  thf(t100_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.77/1.01  thf('14', plain,
% 0.77/1.01      (![X6 : $i, X7 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X6 @ X7)
% 0.77/1.01           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('15', plain,
% 0.77/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/1.01      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/1.01  thf(l32_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/1.01  thf('16', plain,
% 0.77/1.01      (![X3 : $i, X4 : $i]:
% 0.77/1.01         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.77/1.01  thf('17', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         (((k5_xboole_0 @ X0 @ X0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['15', '16'])).
% 0.77/1.01  thf(t92_xboole_1, axiom,
% 0.77/1.01    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.77/1.01  thf('18', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.77/1.01  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.77/1.01      inference('simplify_reflect+', [status(thm)], ['17', '18'])).
% 0.77/1.01  thf(t108_xboole_1, axiom,
% 0.77/1.01    (![A:$i,B:$i,C:$i]:
% 0.77/1.01     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.77/1.01  thf('20', plain,
% 0.77/1.01      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.77/1.01         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ (k3_xboole_0 @ X8 @ X10) @ X9))),
% 0.77/1.01      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.77/1.01  thf('21', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.77/1.01      inference('sup-', [status(thm)], ['19', '20'])).
% 0.77/1.01  thf('22', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.77/1.01      inference('sup+', [status(thm)], ['12', '21'])).
% 0.77/1.01  thf('23', plain,
% 0.77/1.01      (![X3 : $i, X5 : $i]:
% 0.77/1.01         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.77/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.77/1.01  thf('24', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/1.01  thf(t113_zfmisc_1, axiom,
% 0.77/1.01    (![A:$i,B:$i]:
% 0.77/1.01     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.77/1.01       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.77/1.01  thf('25', plain,
% 0.77/1.01      (![X15 : $i, X16 : $i]:
% 0.77/1.01         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.77/1.01          | ((X16) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.01  thf('26', plain,
% 0.77/1.01      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/1.01      inference('simplify', [status(thm)], ['25'])).
% 0.77/1.01  thf('27', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.77/1.01      inference('sup+', [status(thm)], ['12', '21'])).
% 0.77/1.01  thf('28', plain,
% 0.77/1.01      (![X11 : $i, X12 : $i]:
% 0.77/1.01         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.77/1.01      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/1.01  thf('29', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.77/1.01           = (k3_xboole_0 @ X1 @ X0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['27', '28'])).
% 0.77/1.01  thf('30', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('31', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/1.01           = (k3_xboole_0 @ X1 @ X0))),
% 0.77/1.01      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/1.01  thf('32', plain,
% 0.77/1.01      (![X6 : $i, X7 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X6 @ X7)
% 0.77/1.01           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('33', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/1.01           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['31', '32'])).
% 0.77/1.01  thf('34', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/1.01  thf('35', plain,
% 0.77/1.01      (![X6 : $i, X7 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X6 @ X7)
% 0.77/1.01           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/1.01  thf('36', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X0 @ X1)
% 0.77/1.01           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.77/1.01      inference('sup+', [status(thm)], ['34', '35'])).
% 0.77/1.01  thf('37', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/1.01           = (k4_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('demod', [status(thm)], ['33', '36'])).
% 0.77/1.01  thf('38', plain,
% 0.77/1.01      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['11', '24', '26', '37'])).
% 0.77/1.01  thf('39', plain,
% 0.77/1.01      (![X14 : $i, X15 : $i]:
% 0.77/1.01         (((X14) = (k1_xboole_0))
% 0.77/1.01          | ((X15) = (k1_xboole_0))
% 0.77/1.01          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.01  thf('40', plain,
% 0.77/1.01      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 0.77/1.01        | ((sk_B) = (k1_xboole_0)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/1.01  thf('41', plain,
% 0.77/1.01      ((((sk_B) = (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['40'])).
% 0.77/1.01  thf('42', plain,
% 0.77/1.01      (![X3 : $i, X4 : $i]:
% 0.77/1.01         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.77/1.01  thf('43', plain,
% 0.77/1.01      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.01        | ((sk_B) = (k1_xboole_0))
% 0.77/1.01        | (r1_tarski @ sk_A @ sk_C))),
% 0.77/1.01      inference('sup-', [status(thm)], ['41', '42'])).
% 0.77/1.01  thf('44', plain, (((r1_tarski @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['43'])).
% 0.77/1.01  thf('45', plain,
% 0.77/1.01      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('46', plain,
% 0.77/1.01      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.77/1.01      inference('split', [status(esa)], ['45'])).
% 0.77/1.01  thf('47', plain,
% 0.77/1.01      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ X24 @ (k4_xboole_0 @ X21 @ X23))
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X24 @ X21) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X24 @ X23)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('48', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.77/1.01      inference('demod', [status(thm)], ['6', '7'])).
% 0.77/1.01  thf('49', plain,
% 0.77/1.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ X21 @ X23) @ X22)
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ X21 @ X22) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X23 @ X22)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.77/1.01  thf('50', plain,
% 0.77/1.01      (![X0 : $i]:
% 0.77/1.01         ((k2_zfmisc_1 @ (k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ X0) @ 
% 0.77/1.01           (k3_xboole_0 @ sk_D @ sk_B))
% 0.77/1.01           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.77/1.01              (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['48', '49'])).
% 0.77/1.01  thf('51', plain,
% 0.77/1.01      (((k2_zfmisc_1 @ (k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_A) @ 
% 0.77/1.01         (k3_xboole_0 @ sk_D @ sk_B))
% 0.77/1.01         = (k2_zfmisc_1 @ sk_A @ 
% 0.77/1.01            (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B))))),
% 0.77/1.01      inference('sup+', [status(thm)], ['47', '50'])).
% 0.77/1.01  thf('52', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.77/1.01      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/1.01  thf('53', plain,
% 0.77/1.01      (![X15 : $i, X16 : $i]:
% 0.77/1.01         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.77/1.01          | ((X15) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.01  thf('54', plain,
% 0.77/1.01      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.77/1.01      inference('simplify', [status(thm)], ['53'])).
% 0.77/1.01  thf('55', plain,
% 0.77/1.01      (![X0 : $i, X1 : $i]:
% 0.77/1.01         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/1.01           = (k4_xboole_0 @ X0 @ X1))),
% 0.77/1.01      inference('demod', [status(thm)], ['33', '36'])).
% 0.77/1.01  thf('56', plain,
% 0.77/1.01      (((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)))),
% 0.77/1.01      inference('demod', [status(thm)], ['51', '52', '54', '55'])).
% 0.77/1.01  thf('57', plain,
% 0.77/1.01      (![X14 : $i, X15 : $i]:
% 0.77/1.01         (((X14) = (k1_xboole_0))
% 0.77/1.01          | ((X15) = (k1_xboole_0))
% 0.77/1.01          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/1.01  thf('58', plain,
% 0.77/1.01      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.01        | ((sk_A) = (k1_xboole_0))
% 0.77/1.01        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['56', '57'])).
% 0.77/1.01  thf('59', plain,
% 0.77/1.01      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 0.77/1.01        | ((sk_A) = (k1_xboole_0)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['58'])).
% 0.77/1.01  thf('60', plain,
% 0.77/1.01      (![X3 : $i, X4 : $i]:
% 0.77/1.01         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.77/1.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.77/1.01  thf('61', plain,
% 0.77/1.01      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/1.01        | ((sk_A) = (k1_xboole_0))
% 0.77/1.01        | (r1_tarski @ sk_B @ sk_D))),
% 0.77/1.01      inference('sup-', [status(thm)], ['59', '60'])).
% 0.77/1.01  thf('62', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.77/1.01      inference('simplify', [status(thm)], ['61'])).
% 0.77/1.01  thf('63', plain,
% 0.77/1.01      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.77/1.01      inference('split', [status(esa)], ['45'])).
% 0.77/1.01  thf('64', plain,
% 0.77/1.01      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['62', '63'])).
% 0.77/1.01  thf('65', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.77/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/1.01  thf('66', plain,
% 0.77/1.01      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.77/1.01         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.77/1.01      inference('sup-', [status(thm)], ['64', '65'])).
% 0.77/1.01  thf('67', plain,
% 0.77/1.01      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.77/1.01      inference('simplify', [status(thm)], ['53'])).
% 0.77/1.01  thf('68', plain,
% 0.77/1.01      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.77/1.01      inference('demod', [status(thm)], ['66', '67'])).
% 0.77/1.01  thf('69', plain, (((r1_tarski @ sk_B @ sk_D))),
% 0.77/1.01      inference('simplify', [status(thm)], ['68'])).
% 0.77/1.01  thf('70', plain,
% 0.77/1.01      (~ ((r1_tarski @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_B @ sk_D))),
% 0.77/1.01      inference('split', [status(esa)], ['45'])).
% 0.77/1.01  thf('71', plain, (~ ((r1_tarski @ sk_A @ sk_C))),
% 0.77/1.01      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.77/1.01  thf('72', plain, (~ (r1_tarski @ sk_A @ sk_C)),
% 0.77/1.01      inference('simpl_trail', [status(thm)], ['46', '71'])).
% 0.77/1.01  thf('73', plain, (((sk_B) = (k1_xboole_0))),
% 0.77/1.01      inference('clc', [status(thm)], ['44', '72'])).
% 0.77/1.01  thf('74', plain,
% 0.77/1.01      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/1.01      inference('simplify', [status(thm)], ['25'])).
% 0.77/1.01  thf('75', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.77/1.01      inference('demod', [status(thm)], ['0', '73', '74'])).
% 0.77/1.01  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 0.77/1.01  
% 0.77/1.01  % SZS output end Refutation
% 0.77/1.01  
% 0.86/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
