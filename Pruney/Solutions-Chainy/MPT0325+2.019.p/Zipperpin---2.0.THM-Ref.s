%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WBv72NMjz4

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:42 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 249 expanded)
%              Number of leaves         :   21 (  81 expanded)
%              Depth                    :   29
%              Number of atoms          :  902 (2340 expanded)
%              Number of equality atoms :  118 ( 279 expanded)
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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X17 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('7',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X21 @ X23 ) @ X22 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','26'])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ X24 @ ( k4_xboole_0 @ X21 @ X23 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X24 @ X21 ) @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30','37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_B ) )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','58'])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X21 @ X23 ) @ X22 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('61',plain,
    ( ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X15 @ X14 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['68'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['68'])).

thf('79',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['69','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['67','80'])).

thf('82',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('85',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','85'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('89',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','87','88'])).

thf('90',plain,(
    $false ),
    inference(simplify,[status(thm)],['89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WBv72NMjz4
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 428 iterations in 0.269s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(t138_zfmisc_1, conjecture,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.52/0.73       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.73         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.52/0.73          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.73            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.52/0.73  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('1', plain,
% 0.52/0.73      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(t28_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.73  thf('2', plain,
% 0.52/0.73      (![X11 : $i, X12 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.52/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.73         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.73  thf('4', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('5', plain,
% 0.52/0.73      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.52/0.73         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['3', '4'])).
% 0.52/0.73  thf(t123_zfmisc_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.73     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.52/0.73       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         ((k2_zfmisc_1 @ (k3_xboole_0 @ X17 @ X19) @ (k3_xboole_0 @ X18 @ X20))
% 0.52/0.73           = (k3_xboole_0 @ (k2_zfmisc_1 @ X17 @ X18) @ 
% 0.52/0.73              (k2_zfmisc_1 @ X19 @ X20)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.52/0.73         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf(idempotence_k3_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.52/0.73  thf('9', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.52/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.73  thf(t16_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.73       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.73  thf('10', plain,
% 0.52/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.52/0.73           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.52/0.73  thf('11', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ X0 @ X1)
% 0.52/0.73           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf(t100_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.73  thf('13', plain,
% 0.52/0.73      (![X6 : $i, X7 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X6 @ X7)
% 0.52/0.73           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.73  thf('14', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X0 @ X1)
% 0.52/0.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['12', '13'])).
% 0.52/0.73  thf('15', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.52/0.73           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['11', '14'])).
% 0.52/0.73  thf(t92_xboole_1, axiom,
% 0.52/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.52/0.73  thf('16', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ X13) = (k1_xboole_0))),
% 0.52/0.73      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf('18', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.52/0.73      inference('sup+', [status(thm)], ['8', '17'])).
% 0.52/0.73  thf(t125_zfmisc_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.52/0.73         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.52/0.73       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.73         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.73         ((k2_zfmisc_1 @ (k4_xboole_0 @ X21 @ X23) @ X22)
% 0.52/0.73           = (k4_xboole_0 @ (k2_zfmisc_1 @ X21 @ X22) @ 
% 0.52/0.73              (k2_zfmisc_1 @ X23 @ X22)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.52/0.73  thf(l32_xboole_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (![X3 : $i, X4 : $i]:
% 0.52/0.73         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (((k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.52/0.73          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.52/0.73          | (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.52/0.73             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['18', '21'])).
% 0.52/0.73  thf(t113_zfmisc_1, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.52/0.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i]:
% 0.52/0.73         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.52/0.73          | ((X15) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['23'])).
% 0.52/0.73  thf('25', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.73          | (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.52/0.73             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['22', '24'])).
% 0.52/0.73  thf('26', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.52/0.73          (k2_zfmisc_1 @ X1 @ X0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['25'])).
% 0.52/0.73  thf('27', plain,
% 0.52/0.73      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.73        (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['7', '26'])).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      (![X3 : $i, X5 : $i]:
% 0.52/0.73         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.52/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.73         (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B))) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.52/0.73         ((k2_zfmisc_1 @ X24 @ (k4_xboole_0 @ X21 @ X23))
% 0.52/0.73           = (k4_xboole_0 @ (k2_zfmisc_1 @ X24 @ X21) @ 
% 0.52/0.73              (k2_zfmisc_1 @ X24 @ X23)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.52/0.73  thf('31', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ X0 @ X1)
% 0.52/0.73           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k3_xboole_0 @ X0 @ X1)
% 0.52/0.73           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['31', '32'])).
% 0.52/0.73  thf('34', plain,
% 0.52/0.73      (![X6 : $i, X7 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X6 @ X7)
% 0.52/0.73           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.73  thf('35', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.52/0.73           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['33', '34'])).
% 0.52/0.73  thf('36', plain,
% 0.52/0.73      (![X6 : $i, X7 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X6 @ X7)
% 0.52/0.73           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.52/0.73           = (k4_xboole_0 @ X1 @ X0))),
% 0.52/0.73      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.73  thf('38', plain,
% 0.52/0.73      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['29', '30', '37'])).
% 0.52/0.73  thf('39', plain,
% 0.52/0.73      (![X14 : $i, X15 : $i]:
% 0.52/0.73         (((X14) = (k1_xboole_0))
% 0.52/0.73          | ((X15) = (k1_xboole_0))
% 0.52/0.73          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0))
% 0.52/0.73        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['40'])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      (![X3 : $i, X4 : $i]:
% 0.52/0.73         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.52/0.73  thf('43', plain,
% 0.52/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0))
% 0.52/0.73        | (r1_tarski @ sk_B @ sk_D))),
% 0.52/0.73      inference('sup-', [status(thm)], ['41', '42'])).
% 0.52/0.73  thf('44', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['43'])).
% 0.52/0.73  thf('45', plain,
% 0.52/0.73      (![X11 : $i, X12 : $i]:
% 0.52/0.73         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.52/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.73  thf('46', plain,
% 0.52/0.73      ((((sk_A) = (k1_xboole_0)) | ((k3_xboole_0 @ sk_B @ sk_D) = (sk_B)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['44', '45'])).
% 0.52/0.73  thf('47', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      ((((sk_A) = (k1_xboole_0)) | ((k3_xboole_0 @ sk_D @ sk_B) = (sk_B)))),
% 0.52/0.73      inference('demod', [status(thm)], ['46', '47'])).
% 0.52/0.73  thf('49', plain,
% 0.52/0.73      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.52/0.73         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.52/0.73  thf('50', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i]:
% 0.52/0.73         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf('51', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (((k2_zfmisc_1 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.52/0.73          | (r1_tarski @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.73  thf('52', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.52/0.73          | (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ 
% 0.52/0.73             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['50', '51'])).
% 0.52/0.73  thf('53', plain,
% 0.52/0.73      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['23'])).
% 0.52/0.73  thf('54', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.73          | (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ 
% 0.52/0.73             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['52', '53'])).
% 0.52/0.73  thf('55', plain,
% 0.52/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.73         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ 
% 0.52/0.73          (k2_zfmisc_1 @ X1 @ X0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['54'])).
% 0.52/0.73  thf('56', plain,
% 0.52/0.73      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.73        (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['49', '55'])).
% 0.52/0.73  thf('57', plain,
% 0.52/0.73      (![X3 : $i, X5 : $i]:
% 0.52/0.73         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.52/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.52/0.73  thf('58', plain,
% 0.52/0.73      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.73         (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))) = (k1_xboole_0))),
% 0.52/0.73      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.73  thf('59', plain,
% 0.52/0.73      ((((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.52/0.73          (k2_zfmisc_1 @ sk_C @ sk_B)) = (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('sup+', [status(thm)], ['48', '58'])).
% 0.52/0.73  thf('60', plain,
% 0.52/0.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.52/0.73         ((k2_zfmisc_1 @ (k4_xboole_0 @ X21 @ X23) @ X22)
% 0.52/0.73           = (k4_xboole_0 @ (k2_zfmisc_1 @ X21 @ X22) @ 
% 0.52/0.73              (k2_zfmisc_1 @ X23 @ X22)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.52/0.73  thf('61', plain,
% 0.52/0.73      ((((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['59', '60'])).
% 0.52/0.73  thf('62', plain,
% 0.52/0.73      (![X14 : $i, X15 : $i]:
% 0.52/0.73         (((X14) = (k1_xboole_0))
% 0.52/0.73          | ((X15) = (k1_xboole_0))
% 0.52/0.73          | ((k2_zfmisc_1 @ X15 @ X14) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.73  thf('63', plain,
% 0.52/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0))
% 0.52/0.73        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 0.52/0.73        | ((sk_B) = (k1_xboole_0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['61', '62'])).
% 0.52/0.73  thf('64', plain,
% 0.52/0.73      ((((sk_B) = (k1_xboole_0))
% 0.52/0.73        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['63'])).
% 0.52/0.73  thf('65', plain,
% 0.52/0.73      (![X3 : $i, X4 : $i]:
% 0.52/0.73         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.52/0.73  thf('66', plain,
% 0.52/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0))
% 0.52/0.73        | ((sk_B) = (k1_xboole_0))
% 0.52/0.73        | (r1_tarski @ sk_A @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['64', '65'])).
% 0.52/0.73  thf('67', plain,
% 0.52/0.73      (((r1_tarski @ sk_A @ sk_C)
% 0.52/0.73        | ((sk_B) = (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['66'])).
% 0.52/0.73  thf('68', plain,
% 0.52/0.73      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('69', plain,
% 0.52/0.73      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.52/0.73      inference('split', [status(esa)], ['68'])).
% 0.52/0.73  thf('70', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['43'])).
% 0.52/0.73  thf('71', plain,
% 0.52/0.73      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.52/0.73      inference('split', [status(esa)], ['68'])).
% 0.52/0.73  thf('72', plain,
% 0.52/0.73      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['70', '71'])).
% 0.52/0.73  thf('73', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('74', plain,
% 0.52/0.73      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.52/0.73         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['72', '73'])).
% 0.52/0.73  thf('75', plain,
% 0.52/0.73      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['23'])).
% 0.52/0.73  thf('76', plain,
% 0.52/0.73      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.52/0.73      inference('demod', [status(thm)], ['74', '75'])).
% 0.52/0.73  thf('77', plain, (((r1_tarski @ sk_B @ sk_D))),
% 0.52/0.73      inference('simplify', [status(thm)], ['76'])).
% 0.52/0.73  thf('78', plain,
% 0.52/0.73      (~ ((r1_tarski @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_B @ sk_D))),
% 0.52/0.73      inference('split', [status(esa)], ['68'])).
% 0.52/0.73  thf('79', plain, (~ ((r1_tarski @ sk_A @ sk_C))),
% 0.52/0.73      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.52/0.73  thf('80', plain, (~ (r1_tarski @ sk_A @ sk_C)),
% 0.52/0.73      inference('simpl_trail', [status(thm)], ['69', '79'])).
% 0.52/0.73  thf('81', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.52/0.73      inference('clc', [status(thm)], ['67', '80'])).
% 0.52/0.73  thf('82', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('83', plain,
% 0.52/0.73      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.52/0.73        | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['81', '82'])).
% 0.52/0.73  thf('84', plain,
% 0.52/0.73      (![X15 : $i, X16 : $i]:
% 0.52/0.73         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.52/0.73          | ((X16) != (k1_xboole_0)))),
% 0.52/0.73      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.52/0.73  thf('85', plain,
% 0.52/0.73      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['84'])).
% 0.52/0.73  thf('86', plain,
% 0.52/0.73      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.52/0.73      inference('demod', [status(thm)], ['83', '85'])).
% 0.52/0.73  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['86'])).
% 0.52/0.73  thf('88', plain,
% 0.52/0.73      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.52/0.73      inference('simplify', [status(thm)], ['23'])).
% 0.52/0.73  thf('89', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.52/0.73      inference('demod', [status(thm)], ['0', '87', '88'])).
% 0.52/0.73  thf('90', plain, ($false), inference('simplify', [status(thm)], ['89'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
