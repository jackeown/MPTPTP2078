%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vnfQV7IL97

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:41 EST 2020

% Result     : Theorem 52.12s
% Output     : Refutation 52.12s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 929 expanded)
%              Number of leaves         :   25 ( 327 expanded)
%              Depth                    :   42
%              Number of atoms          : 1867 (8229 expanded)
%              Number of equality atoms :  226 ( 919 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
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

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('17',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ( k2_zfmisc_1 @ X32 @ ( k4_xboole_0 @ X29 @ X31 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X32 @ X29 ) @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','40','41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('47',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','59'])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('70',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['62','65','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k4_xboole_0 @ X0 @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['17','70'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('72',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X25 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X23 @ X22 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X3 @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_D ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_D ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_C @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_C @ sk_A )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_D ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','78'])).

thf('80',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('81',plain,
    ( ( ( k4_xboole_0 @ sk_C @ sk_A )
      = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('84',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k4_xboole_0 @ sk_C @ sk_A )
      = sk_C )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('88',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X29 @ X31 ) @ X30 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['62','65','68','69'])).

thf('90',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X3 @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_B @ sk_D )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_D @ sk_B )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ sk_D @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('103',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( ( k4_xboole_0 @ sk_C @ sk_A )
      = sk_C )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','103'])).

thf('105',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('106',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('107',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('112',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_C @ sk_A )
      = sk_C )
    | ( k1_xboole_0 = sk_B ) ),
    inference('sup+',[status(thm)],['104','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('116',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = sk_A )
    | ( ( k4_xboole_0 @ sk_C @ sk_A )
      = sk_C )
    | ( k1_xboole_0 = sk_B ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('118',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( k1_xboole_0 = sk_B )
    | ( ( k4_xboole_0 @ sk_C @ sk_A )
      = sk_C ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['119'])).

thf('121',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('122',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','78'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('124',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('127',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = sk_A )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('129',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_D )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('131',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('133',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B )
      = sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = sk_A ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('135',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['119'])).

thf('137',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = sk_A )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('139',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('141',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X25 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('144',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['139','142','143'])).

thf('145',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('146',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X25 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
        = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('150',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X25 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X25 @ X26 ) @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
        = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['148','151','152'])).

thf('154',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['121','153'])).

thf('155',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['119'])).

thf('158',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['120','158'])).

thf('160',plain,
    ( ( ( k4_xboole_0 @ sk_C @ sk_A )
      = sk_C )
    | ( k1_xboole_0 = sk_B ) ),
    inference(clc,[status(thm)],['118','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','40','41','42','43'])).

thf('162',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = sk_A )
    | ( k1_xboole_0 = sk_B ) ),
    inference('sup+',[status(thm)],['160','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('168',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
    | ( k1_xboole_0 = sk_B ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('171',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) ) )
    | ( k1_xboole_0 = sk_B ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
        = ( k3_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) )
      | ( k1_xboole_0 = sk_B ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X3 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X3 ) @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('175',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
        = k1_xboole_0 )
      | ( k1_xboole_0 = sk_B ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( k1_xboole_0 = sk_B ) ),
    inference('sup+',[status(thm)],['5','176'])).

thf('178',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    k1_xboole_0 = sk_B ),
    inference('simplify_reflect-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_zfmisc_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('181',plain,(
    ! [X23: $i] :
      ( ( k2_zfmisc_1 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','179','181'])).

thf('183',plain,(
    $false ),
    inference(simplify,[status(thm)],['182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vnfQV7IL97
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:43:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.22/0.35  % Python version: Python 3.6.8
% 0.22/0.35  % Running in FO mode
% 52.12/52.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 52.12/52.32  % Solved by: fo/fo7.sh
% 52.12/52.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 52.12/52.32  % done 11934 iterations in 51.857s
% 52.12/52.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 52.12/52.32  % SZS output start Refutation
% 52.12/52.32  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 52.12/52.32  thf(sk_A_type, type, sk_A: $i).
% 52.12/52.32  thf(sk_D_type, type, sk_D: $i).
% 52.12/52.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 52.12/52.32  thf(sk_C_type, type, sk_C: $i).
% 52.12/52.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 52.12/52.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 52.12/52.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 52.12/52.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 52.12/52.32  thf(sk_B_type, type, sk_B: $i).
% 52.12/52.32  thf(t138_zfmisc_1, conjecture,
% 52.12/52.32    (![A:$i,B:$i,C:$i,D:$i]:
% 52.12/52.32     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 52.12/52.32       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 52.12/52.32         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 52.12/52.32  thf(zf_stmt_0, negated_conjecture,
% 52.12/52.32    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 52.12/52.32        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 52.12/52.32          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 52.12/52.32            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 52.12/52.32    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 52.12/52.32  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 52.12/52.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.12/52.32  thf('1', plain,
% 52.12/52.32      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 52.12/52.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.12/52.32  thf(t28_xboole_1, axiom,
% 52.12/52.32    (![A:$i,B:$i]:
% 52.12/52.32     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 52.12/52.32  thf('2', plain,
% 52.12/52.32      (![X15 : $i, X16 : $i]:
% 52.12/52.32         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 52.12/52.32      inference('cnf', [status(esa)], [t28_xboole_1])).
% 52.12/52.32  thf('3', plain,
% 52.12/52.32      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 52.12/52.32      inference('sup-', [status(thm)], ['1', '2'])).
% 52.12/52.32  thf(commutativity_k3_xboole_0, axiom,
% 52.12/52.32    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 52.12/52.32  thf('4', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('5', plain,
% 52.12/52.32      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 52.12/52.32         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 52.12/52.32      inference('demod', [status(thm)], ['3', '4'])).
% 52.12/52.32  thf(t16_xboole_1, axiom,
% 52.12/52.32    (![A:$i,B:$i,C:$i]:
% 52.12/52.32     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 52.12/52.32       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 52.12/52.32  thf('6', plain,
% 52.12/52.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 52.12/52.32           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t16_xboole_1])).
% 52.12/52.32  thf(t100_xboole_1, axiom,
% 52.12/52.32    (![A:$i,B:$i]:
% 52.12/52.32     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 52.12/52.32  thf('7', plain,
% 52.12/52.32      (![X5 : $i, X6 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X5 @ X6)
% 52.12/52.32           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 52.12/52.32  thf('8', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 52.12/52.32           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 52.12/52.32              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 52.12/52.32      inference('sup+', [status(thm)], ['6', '7'])).
% 52.12/52.32  thf('9', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf(t112_xboole_1, axiom,
% 52.12/52.32    (![A:$i,B:$i,C:$i]:
% 52.12/52.32     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 52.12/52.32       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 52.12/52.32  thf('10', plain,
% 52.12/52.32      (![X7 : $i, X8 : $i, X9 : $i]:
% 52.12/52.32         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 52.12/52.32           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 52.12/52.32      inference('cnf', [status(esa)], [t112_xboole_1])).
% 52.12/52.32  thf('11', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.12/52.32         ((k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 52.12/52.32           = (k3_xboole_0 @ (k5_xboole_0 @ X2 @ X0) @ X1))),
% 52.12/52.32      inference('sup+', [status(thm)], ['9', '10'])).
% 52.12/52.32  thf('12', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X1) @ X0)
% 52.12/52.32           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 52.12/52.32      inference('sup+', [status(thm)], ['8', '11'])).
% 52.12/52.32  thf(idempotence_k3_xboole_0, axiom,
% 52.12/52.32    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 52.12/52.32  thf('13', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 52.12/52.32      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 52.12/52.32  thf('14', plain,
% 52.12/52.32      (![X5 : $i, X6 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X5 @ X6)
% 52.12/52.32           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 52.12/52.32  thf('15', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('16', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X1 @ X0)
% 52.12/52.32           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 52.12/52.32  thf(t125_zfmisc_1, axiom,
% 52.12/52.32    (![A:$i,B:$i,C:$i]:
% 52.12/52.32     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 52.12/52.32         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 52.12/52.32       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 52.12/52.32         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 52.12/52.32  thf('17', plain,
% 52.12/52.32      (![X29 : $i, X31 : $i, X32 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ X32 @ (k4_xboole_0 @ X29 @ X31))
% 52.12/52.32           = (k4_xboole_0 @ (k2_zfmisc_1 @ X32 @ X29) @ 
% 52.12/52.32              (k2_zfmisc_1 @ X32 @ X31)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 52.12/52.32  thf('18', plain,
% 52.12/52.32      (![X5 : $i, X6 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X5 @ X6)
% 52.12/52.32           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 52.12/52.32  thf('19', plain,
% 52.12/52.32      (![X7 : $i, X8 : $i, X9 : $i]:
% 52.12/52.32         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 52.12/52.32           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 52.12/52.32      inference('cnf', [status(esa)], [t112_xboole_1])).
% 52.12/52.32  thf(commutativity_k5_xboole_0, axiom,
% 52.12/52.32    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 52.12/52.32  thf('20', plain,
% 52.12/52.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 52.12/52.32  thf('21', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.12/52.32         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0))
% 52.12/52.32           = (k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['19', '20'])).
% 52.12/52.32  thf('22', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 52.12/52.32           = (k3_xboole_0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['18', '21'])).
% 52.12/52.32  thf('23', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 52.12/52.32      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 52.12/52.32  thf('24', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 52.12/52.32           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 52.12/52.32              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 52.12/52.32      inference('sup+', [status(thm)], ['6', '7'])).
% 52.12/52.32  thf('25', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 52.12/52.32           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['23', '24'])).
% 52.12/52.32  thf('26', plain,
% 52.12/52.32      (![X7 : $i, X8 : $i, X9 : $i]:
% 52.12/52.32         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 52.12/52.32           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 52.12/52.32      inference('cnf', [status(esa)], [t112_xboole_1])).
% 52.12/52.32  thf('27', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 52.12/52.32      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 52.12/52.32  thf('28', plain,
% 52.12/52.32      (![X5 : $i, X6 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X5 @ X6)
% 52.12/52.32           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 52.12/52.32  thf('29', plain,
% 52.12/52.32      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['27', '28'])).
% 52.12/52.32  thf('30', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 52.12/52.32           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 52.12/52.32      inference('demod', [status(thm)], ['25', '26', '29'])).
% 52.12/52.32  thf('31', plain,
% 52.12/52.32      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['27', '28'])).
% 52.12/52.32  thf(t92_xboole_1, axiom,
% 52.12/52.32    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 52.12/52.32  thf('32', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 52.12/52.32      inference('cnf', [status(esa)], [t92_xboole_1])).
% 52.12/52.32  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['31', '32'])).
% 52.12/52.32  thf('34', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 52.12/52.32      inference('cnf', [status(esa)], [t92_xboole_1])).
% 52.12/52.32  thf('35', plain,
% 52.12/52.32      (![X7 : $i, X8 : $i, X9 : $i]:
% 52.12/52.32         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 52.12/52.32           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 52.12/52.32      inference('cnf', [status(esa)], [t112_xboole_1])).
% 52.12/52.32  thf('36', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k1_xboole_0) = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['34', '35'])).
% 52.12/52.32  thf('37', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 52.12/52.32      inference('cnf', [status(esa)], [t92_xboole_1])).
% 52.12/52.32  thf('38', plain,
% 52.12/52.32      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 52.12/52.32      inference('demod', [status(thm)], ['36', '37'])).
% 52.12/52.32  thf('39', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 52.12/52.32      inference('sup+', [status(thm)], ['33', '38'])).
% 52.12/52.32  thf('40', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 52.12/52.32      inference('demod', [status(thm)], ['30', '39'])).
% 52.12/52.32  thf('41', plain,
% 52.12/52.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 52.12/52.32  thf('42', plain,
% 52.12/52.32      (![X5 : $i, X6 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X5 @ X6)
% 52.12/52.32           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 52.12/52.32  thf('43', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('44', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['22', '40', '41', '42', '43'])).
% 52.12/52.32  thf('45', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('46', plain,
% 52.12/52.32      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 52.12/52.32         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 52.12/52.32      inference('demod', [status(thm)], ['3', '4'])).
% 52.12/52.32  thf('47', plain,
% 52.12/52.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 52.12/52.32           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t16_xboole_1])).
% 52.12/52.32  thf('48', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 52.12/52.32              (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['46', '47'])).
% 52.12/52.32  thf(t17_xboole_1, axiom,
% 52.12/52.32    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 52.12/52.32  thf('49', plain,
% 52.12/52.32      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 52.12/52.32      inference('cnf', [status(esa)], [t17_xboole_1])).
% 52.12/52.32  thf('50', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (r1_tarski @ (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ 
% 52.12/52.32          (k2_zfmisc_1 @ sk_C @ sk_D))),
% 52.12/52.32      inference('sup+', [status(thm)], ['48', '49'])).
% 52.12/52.32  thf('51', plain,
% 52.12/52.32      (![X15 : $i, X16 : $i]:
% 52.12/52.32         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 52.12/52.32      inference('cnf', [status(esa)], [t28_xboole_1])).
% 52.12/52.32  thf('52', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ 
% 52.12/52.32           (k2_zfmisc_1 @ sk_C @ sk_D))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 52.12/52.32      inference('sup-', [status(thm)], ['50', '51'])).
% 52.12/52.32  thf('53', plain,
% 52.12/52.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 52.12/52.32           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t16_xboole_1])).
% 52.12/52.32  thf('54', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32           (k3_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D)))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 52.12/52.32      inference('demod', [status(thm)], ['52', '53'])).
% 52.12/52.32  thf('55', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('56', plain,
% 52.12/52.32      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 52.12/52.32      inference('cnf', [status(esa)], [t17_xboole_1])).
% 52.12/52.32  thf('57', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 52.12/52.32      inference('sup+', [status(thm)], ['55', '56'])).
% 52.12/52.32  thf('58', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (r1_tarski @ (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ 
% 52.12/52.32          (k3_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['54', '57'])).
% 52.12/52.32  thf('59', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (r1_tarski @ (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ 
% 52.12/52.32          (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['45', '58'])).
% 52.12/52.32  thf('60', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (r1_tarski @ 
% 52.12/52.32          (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32           (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D))) @ 
% 52.12/52.32          k1_xboole_0)),
% 52.12/52.32      inference('sup+', [status(thm)], ['44', '59'])).
% 52.12/52.32  thf('61', plain,
% 52.12/52.32      (![X15 : $i, X16 : $i]:
% 52.12/52.32         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 52.12/52.32      inference('cnf', [status(esa)], [t28_xboole_1])).
% 52.12/52.32  thf('62', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ 
% 52.12/52.32           (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32            (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D))) @ 
% 52.12/52.32           k1_xboole_0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32              (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 52.12/52.32      inference('sup-', [status(thm)], ['60', '61'])).
% 52.12/52.32  thf('63', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('64', plain,
% 52.12/52.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 52.12/52.32           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t16_xboole_1])).
% 52.12/52.32  thf('65', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 52.12/52.32           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['63', '64'])).
% 52.12/52.32  thf('66', plain,
% 52.12/52.32      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 52.12/52.32      inference('demod', [status(thm)], ['36', '37'])).
% 52.12/52.32  thf('67', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('68', plain,
% 52.12/52.32      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['66', '67'])).
% 52.12/52.32  thf('69', plain,
% 52.12/52.32      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['66', '67'])).
% 52.12/52.32  thf('70', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k1_xboole_0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32              (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 52.12/52.32      inference('demod', [status(thm)], ['62', '65', '68', '69'])).
% 52.12/52.32  thf('71', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k1_xboole_0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32              (k2_zfmisc_1 @ sk_C @ (k4_xboole_0 @ X0 @ sk_D))))),
% 52.12/52.32      inference('sup+', [status(thm)], ['17', '70'])).
% 52.12/52.32  thf(t123_zfmisc_1, axiom,
% 52.12/52.32    (![A:$i,B:$i,C:$i,D:$i]:
% 52.12/52.32     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 52.12/52.32       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 52.12/52.32  thf('72', plain,
% 52.12/52.32      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ (k3_xboole_0 @ X25 @ X27) @ (k3_xboole_0 @ X26 @ X28))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X25 @ X26) @ 
% 52.12/52.32              (k2_zfmisc_1 @ X27 @ X28)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 52.12/52.32  thf(t113_zfmisc_1, axiom,
% 52.12/52.32    (![A:$i,B:$i]:
% 52.12/52.32     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 52.12/52.32       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 52.12/52.32  thf('73', plain,
% 52.12/52.32      (![X22 : $i, X23 : $i]:
% 52.12/52.32         (((X22) = (k1_xboole_0))
% 52.12/52.32          | ((X23) = (k1_xboole_0))
% 52.12/52.32          | ((k2_zfmisc_1 @ X23 @ X22) != (k1_xboole_0)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 52.12/52.32  thf('74', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.12/52.32         (((k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 52.12/52.32            != (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ X3 @ X1) = (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ X2 @ X0) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup-', [status(thm)], ['72', '73'])).
% 52.12/52.32  thf('75', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (((k1_xboole_0) != (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_D)) = (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup-', [status(thm)], ['71', '74'])).
% 52.12/52.32  thf('76', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('77', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (((k1_xboole_0) != (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_D)) = (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['75', '76'])).
% 52.12/52.32  thf('78', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_D)) = (k1_xboole_0)))),
% 52.12/52.32      inference('simplify', [status(thm)], ['77'])).
% 52.12/52.32  thf('79', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 52.12/52.32        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['16', '78'])).
% 52.12/52.32  thf('80', plain,
% 52.12/52.32      (![X5 : $i, X6 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X5 @ X6)
% 52.12/52.32           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 52.12/52.32  thf('81', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_C @ sk_A) = (k5_xboole_0 @ sk_C @ k1_xboole_0))
% 52.12/52.32        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['79', '80'])).
% 52.12/52.32  thf('82', plain,
% 52.12/52.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 52.12/52.32  thf('83', plain,
% 52.12/52.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 52.12/52.32  thf(t5_boole, axiom,
% 52.12/52.32    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 52.12/52.32  thf('84', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 52.12/52.32      inference('cnf', [status(esa)], [t5_boole])).
% 52.12/52.32  thf('85', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['83', '84'])).
% 52.12/52.32  thf('86', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))
% 52.12/52.32        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['81', '82', '85'])).
% 52.12/52.32  thf('87', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X1 @ X0)
% 52.12/52.32           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 52.12/52.32  thf('88', plain,
% 52.12/52.32      (![X29 : $i, X30 : $i, X31 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ (k4_xboole_0 @ X29 @ X31) @ X30)
% 52.12/52.32           = (k4_xboole_0 @ (k2_zfmisc_1 @ X29 @ X30) @ 
% 52.12/52.32              (k2_zfmisc_1 @ X31 @ X30)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 52.12/52.32  thf('89', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k1_xboole_0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32              (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D))))),
% 52.12/52.32      inference('demod', [status(thm)], ['62', '65', '68', '69'])).
% 52.12/52.32  thf('90', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k1_xboole_0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32              (k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['88', '89'])).
% 52.12/52.32  thf('91', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.12/52.32         (((k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0))
% 52.12/52.32            != (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ X3 @ X1) = (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ X2 @ X0) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup-', [status(thm)], ['72', '73'])).
% 52.12/52.32  thf('92', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (((k1_xboole_0) != (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup-', [status(thm)], ['90', '91'])).
% 52.12/52.32  thf('93', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('94', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (((k1_xboole_0) != (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)) = (k1_xboole_0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['92', '93'])).
% 52.12/52.32  thf('95', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)) = (k1_xboole_0))
% 52.12/52.32          | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 52.12/52.32      inference('simplify', [status(thm)], ['94'])).
% 52.12/52.32  thf('96', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 52.12/52.32        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['87', '95'])).
% 52.12/52.32  thf('97', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('98', plain,
% 52.12/52.32      (![X5 : $i, X6 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X5 @ X6)
% 52.12/52.32           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 52.12/52.32  thf('99', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X0 @ X1)
% 52.12/52.32           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['97', '98'])).
% 52.12/52.32  thf('100', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_B @ sk_D) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 52.12/52.32        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['96', '99'])).
% 52.12/52.32  thf('101', plain,
% 52.12/52.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 52.12/52.32  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['83', '84'])).
% 52.12/52.32  thf('103', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_B @ sk_D) = (sk_B))
% 52.12/52.32        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['100', '101', '102'])).
% 52.12/52.32  thf('104', plain,
% 52.12/52.32      ((((k1_xboole_0) = (sk_B))
% 52.12/52.32        | ((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))
% 52.12/52.32        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['86', '103'])).
% 52.12/52.32  thf('105', plain,
% 52.12/52.32      (![X5 : $i, X6 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X5 @ X6)
% 52.12/52.32           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 52.12/52.32  thf('106', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 52.12/52.32      inference('cnf', [status(esa)], [t92_xboole_1])).
% 52.12/52.32  thf(t91_xboole_1, axiom,
% 52.12/52.32    (![A:$i,B:$i,C:$i]:
% 52.12/52.32     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 52.12/52.32       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 52.12/52.32  thf('107', plain,
% 52.12/52.32      (![X18 : $i, X19 : $i, X20 : $i]:
% 52.12/52.32         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 52.12/52.32           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 52.12/52.32  thf('108', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 52.12/52.32           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['106', '107'])).
% 52.12/52.32  thf('109', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['83', '84'])).
% 52.12/52.32  thf('110', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['108', '109'])).
% 52.12/52.32  thf('111', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ X1 @ X0)
% 52.12/52.32           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['105', '110'])).
% 52.12/52.32  thf('112', plain,
% 52.12/52.32      ((((k3_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ k1_xboole_0))
% 52.12/52.32        | ((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))
% 52.12/52.32        | ((k1_xboole_0) = (sk_B)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['104', '111'])).
% 52.12/52.32  thf('113', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('114', plain,
% 52.12/52.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 52.12/52.32  thf('115', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['83', '84'])).
% 52.12/52.32  thf('116', plain,
% 52.12/52.32      ((((k3_xboole_0 @ sk_C @ sk_A) = (sk_A))
% 52.12/52.32        | ((k4_xboole_0 @ sk_C @ sk_A) = (sk_C))
% 52.12/52.32        | ((k1_xboole_0) = (sk_B)))),
% 52.12/52.32      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 52.12/52.32  thf('117', plain,
% 52.12/52.32      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 52.12/52.32      inference('cnf', [status(esa)], [t17_xboole_1])).
% 52.12/52.32  thf('118', plain,
% 52.12/52.32      (((r1_tarski @ sk_A @ sk_C)
% 52.12/52.32        | ((k1_xboole_0) = (sk_B))
% 52.12/52.32        | ((k4_xboole_0 @ sk_C @ sk_A) = (sk_C)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['116', '117'])).
% 52.12/52.32  thf('119', plain,
% 52.12/52.32      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 52.12/52.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.12/52.32  thf('120', plain,
% 52.12/52.32      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 52.12/52.32      inference('split', [status(esa)], ['119'])).
% 52.12/52.32  thf('121', plain,
% 52.12/52.32      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 52.12/52.32         (k2_zfmisc_1 @ sk_A @ sk_B)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 52.12/52.32      inference('demod', [status(thm)], ['3', '4'])).
% 52.12/52.32  thf('122', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 52.12/52.32        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['16', '78'])).
% 52.12/52.32  thf('123', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X0 @ X1)
% 52.12/52.32           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['97', '98'])).
% 52.12/52.32  thf('124', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ k1_xboole_0))
% 52.12/52.32        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['122', '123'])).
% 52.12/52.32  thf('125', plain,
% 52.12/52.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 52.12/52.32  thf('126', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['83', '84'])).
% 52.12/52.32  thf('127', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))
% 52.12/52.32        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['124', '125', '126'])).
% 52.12/52.32  thf('128', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k3_xboole_0 @ X1 @ X0)
% 52.12/52.32           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['105', '110'])).
% 52.12/52.32  thf('129', plain,
% 52.12/52.32      ((((k3_xboole_0 @ sk_B @ sk_D) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 52.12/52.32        | ((k4_xboole_0 @ sk_A @ sk_C) = (sk_A)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['127', '128'])).
% 52.12/52.32  thf('130', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('131', plain,
% 52.12/52.32      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 52.12/52.32  thf('132', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['83', '84'])).
% 52.12/52.32  thf('133', plain,
% 52.12/52.32      ((((k3_xboole_0 @ sk_D @ sk_B) = (sk_B))
% 52.12/52.32        | ((k4_xboole_0 @ sk_A @ sk_C) = (sk_A)))),
% 52.12/52.32      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 52.12/52.32  thf('134', plain,
% 52.12/52.32      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 52.12/52.32      inference('cnf', [status(esa)], [t17_xboole_1])).
% 52.12/52.32  thf('135', plain,
% 52.12/52.32      (((r1_tarski @ sk_B @ sk_D) | ((k4_xboole_0 @ sk_A @ sk_C) = (sk_A)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['133', '134'])).
% 52.12/52.32  thf('136', plain,
% 52.12/52.32      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 52.12/52.32      inference('split', [status(esa)], ['119'])).
% 52.12/52.32  thf('137', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_A @ sk_C) = (sk_A)))
% 52.12/52.32         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 52.12/52.32      inference('sup-', [status(thm)], ['135', '136'])).
% 52.12/52.32  thf('138', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k1_xboole_0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32              (k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['88', '89'])).
% 52.12/52.32  thf('139', plain,
% 52.12/52.32      ((((k1_xboole_0)
% 52.12/52.32          = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32             (k2_zfmisc_1 @ sk_A @ sk_D))))
% 52.12/52.32         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['137', '138'])).
% 52.12/52.32  thf('140', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 52.12/52.32      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 52.12/52.32  thf('141', plain,
% 52.12/52.32      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ (k3_xboole_0 @ X25 @ X27) @ (k3_xboole_0 @ X26 @ X28))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X25 @ X26) @ 
% 52.12/52.32              (k2_zfmisc_1 @ X27 @ X28)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 52.12/52.32  thf('142', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['140', '141'])).
% 52.12/52.32  thf('143', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('144', plain,
% 52.12/52.32      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B))))
% 52.12/52.32         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 52.12/52.32      inference('demod', [status(thm)], ['139', '142', '143'])).
% 52.12/52.32  thf('145', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 52.12/52.32      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 52.12/52.32  thf('146', plain,
% 52.12/52.32      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ (k3_xboole_0 @ X25 @ X27) @ (k3_xboole_0 @ X26 @ X28))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X25 @ X26) @ 
% 52.12/52.32              (k2_zfmisc_1 @ X27 @ X28)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 52.12/52.32  thf('147', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['145', '146'])).
% 52.12/52.32  thf('148', plain,
% 52.12/52.32      ((![X0 : $i]:
% 52.12/52.32          ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 52.12/52.32            (k3_xboole_0 @ sk_D @ sk_B))
% 52.12/52.32            = (k3_xboole_0 @ k1_xboole_0 @ 
% 52.12/52.32               (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B)))))
% 52.12/52.32         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['144', '147'])).
% 52.12/52.32  thf('149', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('150', plain,
% 52.12/52.32      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ (k3_xboole_0 @ X25 @ X27) @ (k3_xboole_0 @ X26 @ X28))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X25 @ X26) @ 
% 52.12/52.32              (k2_zfmisc_1 @ X27 @ X28)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 52.12/52.32  thf('151', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X3) @ (k2_zfmisc_1 @ X1 @ X2)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['149', '150'])).
% 52.12/52.32  thf('152', plain,
% 52.12/52.32      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 52.12/52.32      inference('demod', [status(thm)], ['36', '37'])).
% 52.12/52.32  thf('153', plain,
% 52.12/52.32      ((![X0 : $i]:
% 52.12/52.32          ((k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_D) @ 
% 52.12/52.32            (k2_zfmisc_1 @ sk_A @ sk_B)) = (k1_xboole_0)))
% 52.12/52.32         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 52.12/52.32      inference('demod', [status(thm)], ['148', '151', '152'])).
% 52.12/52.32  thf('154', plain,
% 52.12/52.32      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 52.12/52.32         <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['121', '153'])).
% 52.12/52.32  thf('155', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 52.12/52.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.12/52.32  thf('156', plain, (((r1_tarski @ sk_B @ sk_D))),
% 52.12/52.32      inference('simplify_reflect-', [status(thm)], ['154', '155'])).
% 52.12/52.32  thf('157', plain,
% 52.12/52.32      (~ ((r1_tarski @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_B @ sk_D))),
% 52.12/52.32      inference('split', [status(esa)], ['119'])).
% 52.12/52.32  thf('158', plain, (~ ((r1_tarski @ sk_A @ sk_C))),
% 52.12/52.32      inference('sat_resolution*', [status(thm)], ['156', '157'])).
% 52.12/52.32  thf('159', plain, (~ (r1_tarski @ sk_A @ sk_C)),
% 52.12/52.32      inference('simpl_trail', [status(thm)], ['120', '158'])).
% 52.12/52.32  thf('160', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_C @ sk_A) = (sk_C)) | ((k1_xboole_0) = (sk_B)))),
% 52.12/52.32      inference('clc', [status(thm)], ['118', '159'])).
% 52.12/52.32  thf('161', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 52.12/52.32      inference('demod', [status(thm)], ['22', '40', '41', '42', '43'])).
% 52.12/52.32  thf('162', plain,
% 52.12/52.32      (![X5 : $i, X6 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X5 @ X6)
% 52.12/52.32           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 52.12/52.32  thf('163', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 52.12/52.32           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 52.12/52.32      inference('sup+', [status(thm)], ['161', '162'])).
% 52.12/52.32  thf('164', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 52.12/52.32      inference('cnf', [status(esa)], [t5_boole])).
% 52.12/52.32  thf('165', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]:
% 52.12/52.32         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 52.12/52.32      inference('demod', [status(thm)], ['163', '164'])).
% 52.12/52.32  thf('166', plain,
% 52.12/52.32      ((((k4_xboole_0 @ sk_A @ sk_C) = (sk_A)) | ((k1_xboole_0) = (sk_B)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['160', '165'])).
% 52.12/52.32  thf('167', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         ((k1_xboole_0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32              (k2_zfmisc_1 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_D)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['88', '89'])).
% 52.12/52.32  thf('168', plain,
% 52.12/52.32      ((((k1_xboole_0)
% 52.12/52.32          = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 52.12/52.32             (k2_zfmisc_1 @ sk_A @ sk_D)))
% 52.12/52.32        | ((k1_xboole_0) = (sk_B)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['166', '167'])).
% 52.12/52.32  thf('169', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['140', '141'])).
% 52.12/52.32  thf('170', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 52.12/52.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 52.12/52.32  thf('171', plain,
% 52.12/52.32      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B)))
% 52.12/52.32        | ((k1_xboole_0) = (sk_B)))),
% 52.12/52.32      inference('demod', [status(thm)], ['168', '169', '170'])).
% 52.12/52.32  thf('172', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['145', '146'])).
% 52.12/52.32  thf('173', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 52.12/52.32            (k3_xboole_0 @ sk_D @ sk_B))
% 52.12/52.32            = (k3_xboole_0 @ k1_xboole_0 @ 
% 52.12/52.32               (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B))))
% 52.12/52.32          | ((k1_xboole_0) = (sk_B)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['171', '172'])).
% 52.12/52.32  thf('174', plain,
% 52.12/52.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.12/52.32         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X3 @ X2))
% 52.12/52.32           = (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ X3) @ (k2_zfmisc_1 @ X1 @ X2)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['149', '150'])).
% 52.12/52.32  thf('175', plain,
% 52.12/52.32      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 52.12/52.32      inference('demod', [status(thm)], ['36', '37'])).
% 52.12/52.32  thf('176', plain,
% 52.12/52.32      (![X0 : $i]:
% 52.12/52.32         (((k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_D) @ 
% 52.12/52.32            (k2_zfmisc_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 52.12/52.32          | ((k1_xboole_0) = (sk_B)))),
% 52.12/52.32      inference('demod', [status(thm)], ['173', '174', '175'])).
% 52.12/52.32  thf('177', plain,
% 52.12/52.32      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 52.12/52.32        | ((k1_xboole_0) = (sk_B)))),
% 52.12/52.32      inference('sup+', [status(thm)], ['5', '176'])).
% 52.12/52.32  thf('178', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 52.12/52.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.12/52.32  thf('179', plain, (((k1_xboole_0) = (sk_B))),
% 52.12/52.32      inference('simplify_reflect-', [status(thm)], ['177', '178'])).
% 52.12/52.32  thf('180', plain,
% 52.12/52.32      (![X23 : $i, X24 : $i]:
% 52.12/52.32         (((k2_zfmisc_1 @ X23 @ X24) = (k1_xboole_0))
% 52.12/52.32          | ((X24) != (k1_xboole_0)))),
% 52.12/52.32      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 52.12/52.32  thf('181', plain,
% 52.12/52.32      (![X23 : $i]: ((k2_zfmisc_1 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 52.12/52.32      inference('simplify', [status(thm)], ['180'])).
% 52.12/52.32  thf('182', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 52.12/52.32      inference('demod', [status(thm)], ['0', '179', '181'])).
% 52.12/52.32  thf('183', plain, ($false), inference('simplify', [status(thm)], ['182'])).
% 52.12/52.32  
% 52.12/52.32  % SZS output end Refutation
% 52.12/52.32  
% 52.12/52.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
