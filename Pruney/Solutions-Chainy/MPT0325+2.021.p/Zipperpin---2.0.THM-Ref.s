%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWdbWj8lUf

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:42 EST 2020

% Result     : Theorem 3.35s
% Output     : Refutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 393 expanded)
%              Number of leaves         :   23 ( 135 expanded)
%              Depth                    :   22
%              Number of atoms          : 1052 (3234 expanded)
%              Number of equality atoms :  127 ( 395 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X24: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ X27 @ ( k4_xboole_0 @ X24 @ X26 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X24 ) @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X20 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('8',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X24 @ X26 ) @ X25 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X25 ) @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_zfmisc_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('25',plain,(
    ! [X19: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','23','25'])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X18 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('57',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B )
      = sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','46','55','56'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('59',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','68'])).

thf('70',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ X27 @ ( k4_xboole_0 @ X24 @ X26 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X24 ) @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('73',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('74',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X24 @ X26 ) @ X25 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X25 ) @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_D @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('78',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_zfmisc_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77','79'])).

thf('81',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X18 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('85',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('89',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = sk_A )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('91',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ k1_xboole_0 )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = sk_A ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('93',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('97',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['70'])).

thf('99',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['70'])).

thf('101',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['71','101'])).

thf('103',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','102'])).

thf('104',plain,(
    ! [X19: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('105',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','103','104'])).

thf('106',plain,(
    $false ),
    inference(simplify,[status(thm)],['105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZWdbWj8lUf
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.35/3.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.35/3.54  % Solved by: fo/fo7.sh
% 3.35/3.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.35/3.54  % done 2436 iterations in 3.087s
% 3.35/3.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.35/3.54  % SZS output start Refutation
% 3.35/3.54  thf(sk_A_type, type, sk_A: $i).
% 3.35/3.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.35/3.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.35/3.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.35/3.54  thf(sk_D_type, type, sk_D: $i).
% 3.35/3.54  thf(sk_B_type, type, sk_B: $i).
% 3.35/3.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.35/3.54  thf(sk_C_type, type, sk_C: $i).
% 3.35/3.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.35/3.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.35/3.54  thf(t138_zfmisc_1, conjecture,
% 3.35/3.54    (![A:$i,B:$i,C:$i,D:$i]:
% 3.35/3.54     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 3.35/3.54       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 3.35/3.54         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 3.35/3.54  thf(zf_stmt_0, negated_conjecture,
% 3.35/3.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.35/3.54        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 3.35/3.54          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 3.35/3.54            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 3.35/3.54    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 3.35/3.54  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 3.35/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.54  thf(t125_zfmisc_1, axiom,
% 3.35/3.54    (![A:$i,B:$i,C:$i]:
% 3.35/3.54     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 3.35/3.54         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 3.35/3.54       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.35/3.54         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 3.35/3.54  thf('1', plain,
% 3.35/3.54      (![X24 : $i, X26 : $i, X27 : $i]:
% 3.35/3.54         ((k2_zfmisc_1 @ X27 @ (k4_xboole_0 @ X24 @ X26))
% 3.35/3.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X27 @ X24) @ 
% 3.35/3.54              (k2_zfmisc_1 @ X27 @ X26)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 3.35/3.54  thf('2', plain,
% 3.35/3.54      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 3.35/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.54  thf(t28_xboole_1, axiom,
% 3.35/3.54    (![A:$i,B:$i]:
% 3.35/3.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.35/3.54  thf('3', plain,
% 3.35/3.54      (![X8 : $i, X9 : $i]:
% 3.35/3.54         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 3.35/3.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.35/3.54  thf('4', plain,
% 3.35/3.54      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.35/3.54         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.35/3.54      inference('sup-', [status(thm)], ['2', '3'])).
% 3.35/3.54  thf(commutativity_k3_xboole_0, axiom,
% 3.35/3.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.35/3.54  thf('5', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.35/3.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.35/3.54  thf('6', plain,
% 3.35/3.54      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 3.35/3.54         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.35/3.54      inference('demod', [status(thm)], ['4', '5'])).
% 3.35/3.54  thf(t123_zfmisc_1, axiom,
% 3.35/3.54    (![A:$i,B:$i,C:$i,D:$i]:
% 3.35/3.54     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 3.35/3.54       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 3.35/3.54  thf('7', plain,
% 3.35/3.54      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.35/3.54         ((k2_zfmisc_1 @ (k3_xboole_0 @ X20 @ X22) @ (k3_xboole_0 @ X21 @ X23))
% 3.35/3.54           = (k3_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 3.35/3.54              (k2_zfmisc_1 @ X22 @ X23)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 3.35/3.54  thf('8', plain,
% 3.35/3.54      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 3.35/3.54         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.35/3.54      inference('demod', [status(thm)], ['6', '7'])).
% 3.35/3.54  thf('9', plain,
% 3.35/3.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.35/3.54         ((k2_zfmisc_1 @ (k4_xboole_0 @ X24 @ X26) @ X25)
% 3.35/3.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X24 @ X25) @ 
% 3.35/3.54              (k2_zfmisc_1 @ X26 @ X25)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 3.35/3.54  thf('10', plain,
% 3.35/3.54      (![X0 : $i]:
% 3.35/3.54         ((k2_zfmisc_1 @ (k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ X0) @ 
% 3.35/3.54           (k3_xboole_0 @ sk_D @ sk_B))
% 3.35/3.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 3.35/3.54              (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B))))),
% 3.35/3.54      inference('sup+', [status(thm)], ['8', '9'])).
% 3.35/3.54  thf('11', plain,
% 3.35/3.54      (((k2_zfmisc_1 @ (k4_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_A) @ 
% 3.35/3.54         (k3_xboole_0 @ sk_D @ sk_B))
% 3.35/3.54         = (k2_zfmisc_1 @ sk_A @ 
% 3.35/3.54            (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B))))),
% 3.35/3.54      inference('sup+', [status(thm)], ['1', '10'])).
% 3.35/3.54  thf(idempotence_k3_xboole_0, axiom,
% 3.35/3.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 3.35/3.54  thf('12', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 3.35/3.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.35/3.54  thf(t16_xboole_1, axiom,
% 3.35/3.54    (![A:$i,B:$i,C:$i]:
% 3.35/3.54     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 3.35/3.54       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 3.35/3.54  thf('13', plain,
% 3.35/3.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 3.35/3.54           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.35/3.54  thf(t100_xboole_1, axiom,
% 3.35/3.54    (![A:$i,B:$i]:
% 3.35/3.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.35/3.54  thf('14', plain,
% 3.35/3.54      (![X3 : $i, X4 : $i]:
% 3.35/3.54         ((k4_xboole_0 @ X3 @ X4)
% 3.35/3.54           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.35/3.54  thf('15', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.54         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 3.35/3.54           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 3.35/3.54              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 3.35/3.54      inference('sup+', [status(thm)], ['13', '14'])).
% 3.35/3.54  thf('16', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 3.35/3.54           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['12', '15'])).
% 3.35/3.54  thf('17', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 3.35/3.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.35/3.54  thf('18', plain,
% 3.35/3.54      (![X3 : $i, X4 : $i]:
% 3.35/3.54         ((k4_xboole_0 @ X3 @ X4)
% 3.35/3.54           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.35/3.54  thf('19', plain,
% 3.35/3.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['17', '18'])).
% 3.35/3.54  thf('20', plain,
% 3.35/3.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['17', '18'])).
% 3.35/3.54  thf(t92_xboole_1, axiom,
% 3.35/3.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 3.35/3.54  thf('21', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 3.35/3.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.35/3.54  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['20', '21'])).
% 3.35/3.54  thf('23', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 3.35/3.54      inference('demod', [status(thm)], ['16', '19', '22'])).
% 3.35/3.54  thf(t113_zfmisc_1, axiom,
% 3.35/3.54    (![A:$i,B:$i]:
% 3.35/3.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.35/3.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.35/3.54  thf('24', plain,
% 3.35/3.54      (![X18 : $i, X19 : $i]:
% 3.35/3.54         (((k2_zfmisc_1 @ X18 @ X19) = (k1_xboole_0))
% 3.35/3.54          | ((X18) != (k1_xboole_0)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.35/3.54  thf('25', plain,
% 3.35/3.54      (![X19 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 3.35/3.54      inference('simplify', [status(thm)], ['24'])).
% 3.35/3.54  thf('26', plain,
% 3.35/3.54      (((k1_xboole_0)
% 3.35/3.54         = (k2_zfmisc_1 @ sk_A @ 
% 3.35/3.54            (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B))))),
% 3.35/3.54      inference('demod', [status(thm)], ['11', '23', '25'])).
% 3.35/3.54  thf('27', plain,
% 3.35/3.54      (![X17 : $i, X18 : $i]:
% 3.35/3.54         (((X17) = (k1_xboole_0))
% 3.35/3.54          | ((X18) = (k1_xboole_0))
% 3.35/3.54          | ((k2_zfmisc_1 @ X18 @ X17) != (k1_xboole_0)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.35/3.54  thf('28', plain,
% 3.35/3.54      ((((k1_xboole_0) != (k1_xboole_0))
% 3.35/3.54        | ((sk_A) = (k1_xboole_0))
% 3.35/3.54        | ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B)) = (k1_xboole_0)))),
% 3.35/3.54      inference('sup-', [status(thm)], ['26', '27'])).
% 3.35/3.54  thf('29', plain,
% 3.35/3.54      ((((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B)) = (k1_xboole_0))
% 3.35/3.54        | ((sk_A) = (k1_xboole_0)))),
% 3.35/3.54      inference('simplify', [status(thm)], ['28'])).
% 3.35/3.54  thf('30', plain,
% 3.35/3.54      (![X3 : $i, X4 : $i]:
% 3.35/3.54         ((k4_xboole_0 @ X3 @ X4)
% 3.35/3.54           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.35/3.54  thf('31', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 3.35/3.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.35/3.54  thf(t91_xboole_1, axiom,
% 3.35/3.54    (![A:$i,B:$i,C:$i]:
% 3.35/3.54     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 3.35/3.54       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 3.35/3.54  thf('32', plain,
% 3.35/3.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.35/3.54         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 3.35/3.54           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.35/3.54  thf('33', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 3.35/3.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['31', '32'])).
% 3.35/3.54  thf('34', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 3.35/3.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.35/3.54  thf('35', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 3.35/3.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['31', '32'])).
% 3.35/3.54  thf('36', plain,
% 3.35/3.54      (![X0 : $i]:
% 3.35/3.54         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['34', '35'])).
% 3.35/3.54  thf(t5_boole, axiom,
% 3.35/3.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.35/3.54  thf('37', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.35/3.54      inference('cnf', [status(esa)], [t5_boole])).
% 3.35/3.54  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.35/3.54      inference('demod', [status(thm)], ['36', '37'])).
% 3.35/3.54  thf('39', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('demod', [status(thm)], ['33', '38'])).
% 3.35/3.54  thf('40', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ X1 @ X0)
% 3.35/3.54           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['30', '39'])).
% 3.35/3.54  thf('41', plain,
% 3.35/3.54      ((((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B))
% 3.35/3.54          = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 3.35/3.54        | ((sk_A) = (k1_xboole_0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['29', '40'])).
% 3.35/3.54  thf('42', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 3.35/3.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.35/3.54  thf('43', plain,
% 3.35/3.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 3.35/3.54           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t16_xboole_1])).
% 3.35/3.54  thf('44', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.35/3.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.35/3.54  thf('45', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 3.35/3.54           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['43', '44'])).
% 3.35/3.54  thf('46', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.35/3.54           = (k3_xboole_0 @ X1 @ X0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['42', '45'])).
% 3.35/3.54  thf('47', plain,
% 3.35/3.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.35/3.54         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 3.35/3.54           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.35/3.54  thf('48', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 3.35/3.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.35/3.54  thf('49', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 3.35/3.54           = (k1_xboole_0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['47', '48'])).
% 3.35/3.54  thf('50', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('demod', [status(thm)], ['33', '38'])).
% 3.35/3.54  thf('51', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 3.35/3.54           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['49', '50'])).
% 3.35/3.54  thf('52', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.35/3.54      inference('cnf', [status(esa)], [t5_boole])).
% 3.35/3.54  thf('53', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 3.35/3.54      inference('demod', [status(thm)], ['51', '52'])).
% 3.35/3.54  thf('54', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('demod', [status(thm)], ['33', '38'])).
% 3.35/3.54  thf('55', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['53', '54'])).
% 3.35/3.54  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.35/3.54      inference('demod', [status(thm)], ['36', '37'])).
% 3.35/3.54  thf('57', plain,
% 3.35/3.54      ((((k3_xboole_0 @ sk_D @ sk_B) = (sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 3.35/3.54      inference('demod', [status(thm)], ['41', '46', '55', '56'])).
% 3.35/3.54  thf(t36_xboole_1, axiom,
% 3.35/3.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.35/3.54  thf('58', plain,
% 3.35/3.54      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 3.35/3.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.35/3.54  thf('59', plain,
% 3.35/3.54      (![X8 : $i, X9 : $i]:
% 3.35/3.54         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 3.35/3.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.35/3.54  thf('60', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 3.35/3.54           = (k4_xboole_0 @ X0 @ X1))),
% 3.35/3.54      inference('sup-', [status(thm)], ['58', '59'])).
% 3.35/3.54  thf('61', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.35/3.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.35/3.54  thf('62', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.35/3.54           = (k4_xboole_0 @ X0 @ X1))),
% 3.35/3.54      inference('demod', [status(thm)], ['60', '61'])).
% 3.35/3.54  thf('63', plain,
% 3.35/3.54      (![X3 : $i, X4 : $i]:
% 3.35/3.54         ((k4_xboole_0 @ X3 @ X4)
% 3.35/3.54           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.35/3.54  thf('64', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 3.35/3.54           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['62', '63'])).
% 3.35/3.54  thf('65', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ X1 @ X0)
% 3.35/3.54           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['30', '39'])).
% 3.35/3.54  thf('66', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ X1 @ X0)
% 3.35/3.54           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['64', '65'])).
% 3.35/3.54  thf('67', plain,
% 3.35/3.54      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 3.35/3.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.35/3.54  thf('68', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 3.35/3.54      inference('sup+', [status(thm)], ['66', '67'])).
% 3.35/3.54  thf('69', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['57', '68'])).
% 3.35/3.54  thf('70', plain,
% 3.35/3.54      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 3.35/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.54  thf('71', plain,
% 3.35/3.54      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 3.35/3.54      inference('split', [status(esa)], ['70'])).
% 3.35/3.54  thf('72', plain,
% 3.35/3.54      (![X24 : $i, X26 : $i, X27 : $i]:
% 3.35/3.54         ((k2_zfmisc_1 @ X27 @ (k4_xboole_0 @ X24 @ X26))
% 3.35/3.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X27 @ X24) @ 
% 3.35/3.54              (k2_zfmisc_1 @ X27 @ X26)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 3.35/3.54  thf('73', plain,
% 3.35/3.54      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 3.35/3.54         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.35/3.54      inference('demod', [status(thm)], ['6', '7'])).
% 3.35/3.54  thf('74', plain,
% 3.35/3.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.35/3.54         ((k2_zfmisc_1 @ (k4_xboole_0 @ X24 @ X26) @ X25)
% 3.35/3.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X24 @ X25) @ 
% 3.35/3.54              (k2_zfmisc_1 @ X26 @ X25)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 3.35/3.54  thf('75', plain,
% 3.35/3.54      (![X0 : $i]:
% 3.35/3.54         ((k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 3.35/3.54           (k3_xboole_0 @ sk_D @ sk_B))
% 3.35/3.54           = (k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B)) @ 
% 3.35/3.54              (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['73', '74'])).
% 3.35/3.54  thf('76', plain,
% 3.35/3.54      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 3.35/3.54         (k3_xboole_0 @ sk_D @ sk_B))
% 3.35/3.54         = (k2_zfmisc_1 @ sk_A @ 
% 3.35/3.54            (k4_xboole_0 @ (k3_xboole_0 @ sk_D @ sk_B) @ sk_B)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['72', '75'])).
% 3.35/3.54  thf('77', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 3.35/3.54      inference('demod', [status(thm)], ['16', '19', '22'])).
% 3.35/3.54  thf('78', plain,
% 3.35/3.54      (![X18 : $i, X19 : $i]:
% 3.35/3.54         (((k2_zfmisc_1 @ X18 @ X19) = (k1_xboole_0))
% 3.35/3.54          | ((X19) != (k1_xboole_0)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.35/3.54  thf('79', plain,
% 3.35/3.54      (![X18 : $i]: ((k2_zfmisc_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 3.35/3.54      inference('simplify', [status(thm)], ['78'])).
% 3.35/3.54  thf('80', plain,
% 3.35/3.54      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 3.35/3.54         (k3_xboole_0 @ sk_D @ sk_B)) = (k1_xboole_0))),
% 3.35/3.54      inference('demod', [status(thm)], ['76', '77', '79'])).
% 3.35/3.54  thf('81', plain,
% 3.35/3.54      (![X17 : $i, X18 : $i]:
% 3.35/3.54         (((X17) = (k1_xboole_0))
% 3.35/3.54          | ((X18) = (k1_xboole_0))
% 3.35/3.54          | ((k2_zfmisc_1 @ X18 @ X17) != (k1_xboole_0)))),
% 3.35/3.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.35/3.54  thf('82', plain,
% 3.35/3.54      ((((k1_xboole_0) != (k1_xboole_0))
% 3.35/3.54        | ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0))
% 3.35/3.54        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 3.35/3.54      inference('sup-', [status(thm)], ['80', '81'])).
% 3.35/3.54  thf('83', plain,
% 3.35/3.54      ((((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))
% 3.35/3.54        | ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)) = (k1_xboole_0)))),
% 3.35/3.54      inference('simplify', [status(thm)], ['82'])).
% 3.35/3.54  thf('84', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ X1 @ X0)
% 3.35/3.54           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['30', '39'])).
% 3.35/3.54  thf('85', plain,
% 3.35/3.54      ((((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A))
% 3.35/3.54          = (k5_xboole_0 @ sk_A @ k1_xboole_0))
% 3.35/3.54        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['83', '84'])).
% 3.35/3.54  thf('86', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]:
% 3.35/3.54         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.35/3.54           = (k3_xboole_0 @ X1 @ X0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['42', '45'])).
% 3.35/3.54  thf('87', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.35/3.54      inference('sup+', [status(thm)], ['53', '54'])).
% 3.35/3.54  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.35/3.54      inference('demod', [status(thm)], ['36', '37'])).
% 3.35/3.54  thf('89', plain,
% 3.35/3.54      ((((k3_xboole_0 @ sk_C @ sk_A) = (sk_A))
% 3.35/3.54        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 3.35/3.54      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 3.35/3.54  thf('90', plain,
% 3.35/3.54      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 3.35/3.54         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.35/3.54      inference('demod', [status(thm)], ['6', '7'])).
% 3.35/3.54  thf('91', plain,
% 3.35/3.54      ((((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ k1_xboole_0)
% 3.35/3.54          = (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.35/3.54        | ((k3_xboole_0 @ sk_C @ sk_A) = (sk_A)))),
% 3.35/3.54      inference('sup+', [status(thm)], ['89', '90'])).
% 3.35/3.54  thf('92', plain,
% 3.35/3.54      (![X18 : $i]: ((k2_zfmisc_1 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 3.35/3.54      inference('simplify', [status(thm)], ['78'])).
% 3.35/3.54  thf('93', plain,
% 3.35/3.54      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.35/3.54        | ((k3_xboole_0 @ sk_C @ sk_A) = (sk_A)))),
% 3.35/3.54      inference('demod', [status(thm)], ['91', '92'])).
% 3.35/3.54  thf('94', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 3.35/3.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.35/3.54  thf('95', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 3.35/3.54      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 3.35/3.54  thf('96', plain,
% 3.35/3.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 3.35/3.54      inference('sup+', [status(thm)], ['66', '67'])).
% 3.35/3.54  thf('97', plain, ((r1_tarski @ sk_A @ sk_C)),
% 3.35/3.54      inference('sup+', [status(thm)], ['95', '96'])).
% 3.35/3.54  thf('98', plain,
% 3.35/3.54      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 3.35/3.54      inference('split', [status(esa)], ['70'])).
% 3.35/3.54  thf('99', plain, (((r1_tarski @ sk_A @ sk_C))),
% 3.35/3.54      inference('sup-', [status(thm)], ['97', '98'])).
% 3.35/3.54  thf('100', plain,
% 3.35/3.54      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C))),
% 3.35/3.54      inference('split', [status(esa)], ['70'])).
% 3.35/3.54  thf('101', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 3.35/3.54      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 3.35/3.54  thf('102', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 3.35/3.54      inference('simpl_trail', [status(thm)], ['71', '101'])).
% 3.35/3.54  thf('103', plain, (((sk_A) = (k1_xboole_0))),
% 3.35/3.54      inference('sup-', [status(thm)], ['69', '102'])).
% 3.35/3.54  thf('104', plain,
% 3.35/3.54      (![X19 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 3.35/3.54      inference('simplify', [status(thm)], ['24'])).
% 3.35/3.54  thf('105', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 3.35/3.54      inference('demod', [status(thm)], ['0', '103', '104'])).
% 3.35/3.54  thf('106', plain, ($false), inference('simplify', [status(thm)], ['105'])).
% 3.35/3.54  
% 3.35/3.54  % SZS output end Refutation
% 3.35/3.54  
% 3.35/3.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
