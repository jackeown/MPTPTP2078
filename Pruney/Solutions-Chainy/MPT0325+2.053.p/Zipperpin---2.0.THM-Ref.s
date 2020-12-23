%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ukoam3aCHf

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 153 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   27
%              Number of atoms          :  840 (1421 expanded)
%              Number of equality atoms :  102 ( 160 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X17 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ X24 @ ( k4_xboole_0 @ X21 @ X23 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X21 ) @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X21 @ X23 ) @ X22 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k3_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('39',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X21 @ X23 ) @ X22 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ X24 @ ( k4_xboole_0 @ X21 @ X23 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X21 ) @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('51',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_D )
      = sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['35'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('74',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['35'])).

thf('77',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['36','77'])).

thf('79',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['34','78'])).

thf('80',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('81',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','79','80'])).

thf('82',plain,(
    $false ),
    inference(simplify,[status(thm)],['81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ukoam3aCHf
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 212 iterations in 0.102s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(t138_zfmisc_1, conjecture,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.19/0.55       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.55         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.19/0.55          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.55            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.19/0.55  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t28_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      (![X11 : $i, X12 : $i]:
% 0.19/0.55         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.19/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.55         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.55  thf(t123_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.19/0.55       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.55         ((k2_zfmisc_1 @ (k3_xboole_0 @ X17 @ X19) @ (k3_xboole_0 @ X18 @ X20))
% 0.19/0.55           = (k3_xboole_0 @ (k2_zfmisc_1 @ X17 @ X18) @ 
% 0.19/0.55              (k2_zfmisc_1 @ X19 @ X20)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.19/0.55         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.19/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.55  thf(t17_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.19/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.55  thf(l32_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (![X1 : $i, X3 : $i]:
% 0.19/0.55         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.19/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.55  thf(t125_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.19/0.55         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.19/0.55       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.55         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.19/0.55         ((k2_zfmisc_1 @ X24 @ (k4_xboole_0 @ X21 @ X23))
% 0.19/0.55           = (k4_xboole_0 @ (k2_zfmisc_1 @ X24 @ X21) @ 
% 0.19/0.55              (k2_zfmisc_1 @ X24 @ X23)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      (![X1 : $i, X2 : $i]:
% 0.19/0.55         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (((k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.19/0.55          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.55  thf('12', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (((k2_zfmisc_1 @ X2 @ k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.19/0.55             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.19/0.55  thf(t113_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (![X15 : $i, X16 : $i]:
% 0.19/0.55         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.19/0.55          | ((X16) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.19/0.55             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['12', '14'])).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.19/0.55          (k2_zfmisc_1 @ X2 @ X0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.55        (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.19/0.55      inference('sup+', [status(thm)], ['5', '16'])).
% 0.19/0.55  thf('18', plain,
% 0.19/0.55      (![X1 : $i, X3 : $i]:
% 0.19/0.55         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.19/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.55         (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)) = (k1_xboole_0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.55         ((k2_zfmisc_1 @ (k4_xboole_0 @ X21 @ X23) @ X22)
% 0.19/0.55           = (k4_xboole_0 @ (k2_zfmisc_1 @ X21 @ X22) @ 
% 0.19/0.55              (k2_zfmisc_1 @ X23 @ X22)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.19/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.55  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.55  thf(t16_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.55       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.55         ((k3_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8)
% 0.19/0.55           = (k3_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k3_xboole_0 @ X0 @ X1)
% 0.19/0.55           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.55  thf(t100_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      (![X4 : $i, X5 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X4 @ X5)
% 0.19/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.55           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['23', '24'])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (![X4 : $i, X5 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X4 @ X5)
% 0.19/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.55           = (k4_xboole_0 @ X1 @ X0))),
% 0.19/0.55      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.55  thf('28', plain,
% 0.19/0.55      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.19/0.55      inference('demod', [status(thm)], ['19', '20', '27'])).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      (![X14 : $i, X15 : $i]:
% 0.19/0.55         (((X14) = (k1_xboole_0))
% 0.19/0.55          | ((X15) = (k1_xboole_0))
% 0.19/0.55          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 0.19/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      ((((sk_B) = (k1_xboole_0))
% 0.19/0.55        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      (![X1 : $i, X2 : $i]:
% 0.19/0.55         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.55  thf('33', plain,
% 0.19/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55        | ((sk_B) = (k1_xboole_0))
% 0.19/0.55        | (r1_tarski @ sk_A @ sk_C))),
% 0.19/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.55  thf('34', plain, (((r1_tarski @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.19/0.55      inference('split', [status(esa)], ['35'])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.19/0.55         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.19/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.55         ((k2_zfmisc_1 @ (k4_xboole_0 @ X21 @ X23) @ X22)
% 0.19/0.55           = (k4_xboole_0 @ (k2_zfmisc_1 @ X21 @ X22) @ 
% 0.19/0.55              (k2_zfmisc_1 @ X23 @ X22)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.19/0.55  thf('40', plain,
% 0.19/0.55      (![X1 : $i, X2 : $i]:
% 0.19/0.55         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.55  thf('41', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (((k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.19/0.55          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.55  thf('42', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.19/0.55          | (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ 
% 0.19/0.55             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['38', '41'])).
% 0.19/0.55  thf('43', plain,
% 0.19/0.55      (![X15 : $i, X16 : $i]:
% 0.19/0.55         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.19/0.55          | ((X15) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.55  thf('44', plain,
% 0.19/0.55      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.55  thf('45', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55          | (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ 
% 0.19/0.55             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['42', '44'])).
% 0.19/0.55  thf('46', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ 
% 0.19/0.55          (k2_zfmisc_1 @ X1 @ X0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.19/0.55  thf('47', plain,
% 0.19/0.55      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.55        (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['37', '46'])).
% 0.19/0.55  thf('48', plain,
% 0.19/0.55      (![X1 : $i, X3 : $i]:
% 0.19/0.55         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.19/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.55  thf('49', plain,
% 0.19/0.55      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.19/0.55         (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D))) = (k1_xboole_0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.55  thf('50', plain,
% 0.19/0.55      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.19/0.55         ((k2_zfmisc_1 @ X24 @ (k4_xboole_0 @ X21 @ X23))
% 0.19/0.55           = (k4_xboole_0 @ (k2_zfmisc_1 @ X24 @ X21) @ 
% 0.19/0.55              (k2_zfmisc_1 @ X24 @ X23)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.19/0.55  thf('51', plain,
% 0.19/0.55      (((k2_zfmisc_1 @ sk_A @ 
% 0.19/0.55         (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))) = (k1_xboole_0))),
% 0.19/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.55  thf('52', plain,
% 0.19/0.55      (![X14 : $i, X15 : $i]:
% 0.19/0.55         (((X14) = (k1_xboole_0))
% 0.19/0.55          | ((X15) = (k1_xboole_0))
% 0.19/0.55          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.55  thf('53', plain,
% 0.19/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0))
% 0.19/0.55        | ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.55  thf('54', plain,
% 0.19/0.55      ((((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['53'])).
% 0.19/0.55  thf('55', plain,
% 0.19/0.55      (![X1 : $i, X2 : $i]:
% 0.19/0.55         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.55  thf('56', plain,
% 0.19/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0))
% 0.19/0.55        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.19/0.55  thf('57', plain,
% 0.19/0.55      (((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.19/0.55  thf('58', plain,
% 0.19/0.55      (![X11 : $i, X12 : $i]:
% 0.19/0.55         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.19/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.55  thf('59', plain,
% 0.19/0.55      ((((sk_A) = (k1_xboole_0))
% 0.19/0.55        | ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D)) = (sk_B)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.55  thf('60', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k3_xboole_0 @ X0 @ X1)
% 0.19/0.55           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['21', '22'])).
% 0.19/0.55  thf('61', plain,
% 0.19/0.55      ((((sk_A) = (k1_xboole_0)) | ((k3_xboole_0 @ sk_B @ sk_D) = (sk_B)))),
% 0.19/0.55      inference('demod', [status(thm)], ['59', '60'])).
% 0.19/0.55  thf('62', plain,
% 0.19/0.55      (![X4 : $i, X5 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X4 @ X5)
% 0.19/0.55           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.55  thf('63', plain,
% 0.19/0.55      ((((k4_xboole_0 @ sk_B @ sk_D) = (k5_xboole_0 @ sk_B @ sk_B))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.55  thf(t92_xboole_1, axiom,
% 0.19/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.55  thf('64', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.55  thf('65', plain,
% 0.19/0.55      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['63', '64'])).
% 0.19/0.55  thf('66', plain,
% 0.19/0.55      (![X1 : $i, X2 : $i]:
% 0.19/0.55         ((r1_tarski @ X1 @ X2) | ((k4_xboole_0 @ X1 @ X2) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.55  thf('67', plain,
% 0.19/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.55        | ((sk_A) = (k1_xboole_0))
% 0.19/0.55        | (r1_tarski @ sk_B @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.19/0.55  thf('68', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['67'])).
% 0.19/0.55  thf('69', plain,
% 0.19/0.55      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.19/0.55      inference('split', [status(esa)], ['35'])).
% 0.19/0.55  thf('70', plain,
% 0.19/0.55      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.19/0.55  thf('71', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('72', plain,
% 0.19/0.55      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.19/0.55         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['70', '71'])).
% 0.19/0.55  thf('73', plain,
% 0.19/0.55      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.55  thf('74', plain,
% 0.19/0.55      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.19/0.55      inference('demod', [status(thm)], ['72', '73'])).
% 0.19/0.55  thf('75', plain, (((r1_tarski @ sk_B @ sk_D))),
% 0.19/0.55      inference('simplify', [status(thm)], ['74'])).
% 0.19/0.55  thf('76', plain,
% 0.19/0.55      (~ ((r1_tarski @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_B @ sk_D))),
% 0.19/0.55      inference('split', [status(esa)], ['35'])).
% 0.19/0.55  thf('77', plain, (~ ((r1_tarski @ sk_A @ sk_C))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['75', '76'])).
% 0.19/0.55  thf('78', plain, (~ (r1_tarski @ sk_A @ sk_C)),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['36', '77'])).
% 0.19/0.55  thf('79', plain, (((sk_B) = (k1_xboole_0))),
% 0.19/0.55      inference('clc', [status(thm)], ['34', '78'])).
% 0.19/0.55  thf('80', plain,
% 0.19/0.55      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.55  thf('81', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.55      inference('demod', [status(thm)], ['0', '79', '80'])).
% 0.19/0.55  thf('82', plain, ($false), inference('simplify', [status(thm)], ['81'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
