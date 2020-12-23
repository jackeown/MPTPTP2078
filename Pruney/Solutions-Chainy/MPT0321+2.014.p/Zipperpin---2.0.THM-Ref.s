%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJsfkTQfFt

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:34 EST 2020

% Result     : Theorem 1.08s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :  167 (2420 expanded)
%              Number of leaves         :   16 ( 763 expanded)
%              Depth                    :   33
%              Number of atoms          : 1465 (27721 expanded)
%              Number of equality atoms :  159 (3528 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('2',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X13 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X13 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X1 ) @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) )
      = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('36',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['16','38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('43',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('47',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_B )
    | ( sk_D = sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X1 ) @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('57',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( ( k3_xboole_0 @ sk_C @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('64',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X13 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('70',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('75',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('77',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( sk_B
      = ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( sk_B
      = ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('80',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('82',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('83',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ sk_D )
      = ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ sk_D )
      = ( k2_zfmisc_1 @ sk_C @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','85'])).

thf('87',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_C @ sk_D )
      = ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X11 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('95',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_C @ sk_A )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_C @ sk_D )
      = ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('99',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X11 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('106',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( sk_C = sk_A )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['97','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('109',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('110',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X11 @ X10 ) @ ( k2_zfmisc_1 @ X12 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( ( k3_xboole_0 @ sk_D @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_B ) ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('114',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('120',plain,
    ( ( r1_tarski @ sk_A @ k1_xboole_0 )
    | ( sk_C = sk_A )
    | ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','119'])).

thf('121',plain,
    ( ( sk_C = sk_A )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['97','106'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('123',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_C = sk_A ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('125',plain,
    ( ( sk_C = sk_A )
    | ~ ( r1_tarski @ sk_A @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( sk_C = sk_A )
    | ~ ( r1_tarski @ sk_A @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_A ) ),
    inference(clc,[status(thm)],['120','127'])).

thf('129',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('130',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = sk_A ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    sk_C = sk_A ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['50'])).

thf('134',plain,
    ( ( sk_C != sk_C )
   <= ( sk_A != sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    sk_A = sk_C ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['50'])).

thf('137',plain,(
    sk_B != sk_D ),
    inference('sat_resolution*',[status(thm)],['135','136'])).

thf('138',plain,(
    sk_B != sk_D ),
    inference(simpl_trail,[status(thm)],['51','137'])).

thf('139',plain,(
    ~ ( r1_tarski @ sk_D @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['49','138'])).

thf('140',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('141',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['143','144'])).

thf('146',plain,(
    sk_C = sk_A ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    r1_tarski @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['140','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['139','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJsfkTQfFt
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.08/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.08/1.27  % Solved by: fo/fo7.sh
% 1.08/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.08/1.27  % done 843 iterations in 0.789s
% 1.08/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.08/1.27  % SZS output start Refutation
% 1.08/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.08/1.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.08/1.27  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.08/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.08/1.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.08/1.27  thf(sk_D_type, type, sk_D: $i).
% 1.08/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.08/1.27  thf(sk_C_type, type, sk_C: $i).
% 1.08/1.27  thf(idempotence_k3_xboole_0, axiom,
% 1.08/1.27    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.08/1.27  thf('0', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.08/1.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.08/1.27  thf('1', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.08/1.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.08/1.27  thf(t134_zfmisc_1, conjecture,
% 1.08/1.27    (![A:$i,B:$i,C:$i,D:$i]:
% 1.08/1.27     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.08/1.27       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.08/1.27         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 1.08/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.08/1.27    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.08/1.27        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.08/1.27          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.08/1.27            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 1.08/1.27    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 1.08/1.27  thf('2', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf(t123_zfmisc_1, axiom,
% 1.08/1.27    (![A:$i,B:$i,C:$i,D:$i]:
% 1.08/1.27     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 1.08/1.27       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 1.08/1.27  thf('3', plain,
% 1.08/1.27      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ (k3_xboole_0 @ X13 @ X15) @ (k3_xboole_0 @ X14 @ X16))
% 1.08/1.27           = (k3_xboole_0 @ (k2_zfmisc_1 @ X13 @ X14) @ 
% 1.08/1.27              (k2_zfmisc_1 @ X15 @ X16)))),
% 1.08/1.27      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.08/1.27  thf('4', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 1.08/1.27           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 1.08/1.27              (k2_zfmisc_1 @ X1 @ X0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['2', '3'])).
% 1.08/1.27  thf('5', plain,
% 1.08/1.27      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ (k3_xboole_0 @ X13 @ X15) @ (k3_xboole_0 @ X14 @ X16))
% 1.08/1.27           = (k3_xboole_0 @ (k2_zfmisc_1 @ X13 @ X14) @ 
% 1.08/1.27              (k2_zfmisc_1 @ X15 @ X16)))),
% 1.08/1.27      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.08/1.27  thf('6', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X1) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ X0)))),
% 1.08/1.27      inference('demod', [status(thm)], ['4', '5'])).
% 1.08/1.27  thf('7', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ X0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['1', '6'])).
% 1.08/1.27  thf('8', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_D))
% 1.08/1.27         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 1.08/1.27      inference('sup+', [status(thm)], ['0', '7'])).
% 1.08/1.27  thf(commutativity_k3_xboole_0, axiom,
% 1.08/1.27    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.08/1.27  thf('9', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.08/1.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.27  thf('10', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B))
% 1.08/1.27         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 1.08/1.27      inference('demod', [status(thm)], ['8', '9'])).
% 1.08/1.27  thf('11', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf(t117_zfmisc_1, axiom,
% 1.08/1.27    (![A:$i,B:$i,C:$i]:
% 1.08/1.27     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.08/1.27          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 1.08/1.27            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 1.08/1.27          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 1.08/1.27  thf('12', plain,
% 1.08/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.08/1.27         (((X10) = (k1_xboole_0))
% 1.08/1.27          | (r1_tarski @ X11 @ X12)
% 1.08/1.27          | ~ (r1_tarski @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 1.08/1.27               (k2_zfmisc_1 @ X10 @ X12)))),
% 1.08/1.27      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.08/1.27  thf('13', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 1.08/1.27             (k2_zfmisc_1 @ sk_A @ X0))
% 1.08/1.27          | (r1_tarski @ sk_B @ X0)
% 1.08/1.27          | ((sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['11', '12'])).
% 1.08/1.27  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('15', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 1.08/1.27             (k2_zfmisc_1 @ sk_A @ X0))
% 1.08/1.27          | (r1_tarski @ sk_B @ X0))),
% 1.08/1.27      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 1.08/1.27  thf('16', plain,
% 1.08/1.27      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 1.08/1.27           (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D))
% 1.08/1.27        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['10', '15'])).
% 1.08/1.27  thf('17', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.08/1.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.27  thf(t17_xboole_1, axiom,
% 1.08/1.27    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.08/1.27  thf('18', plain,
% 1.08/1.27      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 1.08/1.27      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.08/1.27  thf('19', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.08/1.27      inference('sup+', [status(thm)], ['17', '18'])).
% 1.08/1.27  thf(t28_xboole_1, axiom,
% 1.08/1.27    (![A:$i,B:$i]:
% 1.08/1.27     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.08/1.27  thf('20', plain,
% 1.08/1.27      (![X8 : $i, X9 : $i]:
% 1.08/1.27         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 1.08/1.27      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.08/1.27  thf('21', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]:
% 1.08/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.08/1.27           = (k3_xboole_0 @ X1 @ X0))),
% 1.08/1.27      inference('sup-', [status(thm)], ['19', '20'])).
% 1.08/1.27  thf('22', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.08/1.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.27  thf('23', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]:
% 1.08/1.27         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.08/1.27           = (k3_xboole_0 @ X1 @ X0))),
% 1.08/1.27      inference('demod', [status(thm)], ['21', '22'])).
% 1.08/1.27  thf('24', plain,
% 1.08/1.27      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 1.08/1.27      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.08/1.27  thf('25', plain,
% 1.08/1.27      (![X8 : $i, X9 : $i]:
% 1.08/1.27         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 1.08/1.27      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.08/1.27  thf('26', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]:
% 1.08/1.27         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.08/1.27           = (k3_xboole_0 @ X0 @ X1))),
% 1.08/1.27      inference('sup-', [status(thm)], ['24', '25'])).
% 1.08/1.27  thf('27', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.08/1.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.27  thf('28', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]:
% 1.08/1.27         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.08/1.27           = (k3_xboole_0 @ X0 @ X1))),
% 1.08/1.27      inference('demod', [status(thm)], ['26', '27'])).
% 1.08/1.27  thf('29', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ X0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['1', '6'])).
% 1.08/1.27  thf('30', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ sk_A @ 
% 1.08/1.27           (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D @ X0)))
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ X0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['28', '29'])).
% 1.08/1.27  thf('31', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ X0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['1', '6'])).
% 1.08/1.27  thf('32', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ sk_A @ 
% 1.08/1.27           (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_D @ X0)))
% 1.08/1.27           = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.08/1.27      inference('demod', [status(thm)], ['30', '31'])).
% 1.08/1.27  thf('33', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B))
% 1.08/1.27         = (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_B)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['23', '32'])).
% 1.08/1.27  thf('34', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B))
% 1.08/1.27         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 1.08/1.27      inference('demod', [status(thm)], ['8', '9'])).
% 1.08/1.27  thf('35', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.08/1.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.08/1.27  thf('36', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D)
% 1.08/1.27         = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.08/1.27      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.08/1.27  thf('37', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('38', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D)
% 1.08/1.27         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('demod', [status(thm)], ['36', '37'])).
% 1.08/1.27  thf(d10_xboole_0, axiom,
% 1.08/1.27    (![A:$i,B:$i]:
% 1.08/1.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.08/1.27  thf('39', plain,
% 1.08/1.27      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 1.08/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.08/1.27  thf('40', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 1.08/1.27      inference('simplify', [status(thm)], ['39'])).
% 1.08/1.27  thf('41', plain, ((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B))),
% 1.08/1.27      inference('demod', [status(thm)], ['16', '38', '40'])).
% 1.08/1.27  thf('42', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.08/1.27      inference('sup+', [status(thm)], ['17', '18'])).
% 1.08/1.27  thf('43', plain,
% 1.08/1.27      (![X3 : $i, X5 : $i]:
% 1.08/1.27         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 1.08/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.08/1.27  thf('44', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]:
% 1.08/1.27         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.08/1.27          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['42', '43'])).
% 1.08/1.27  thf('45', plain, (((sk_B) = (k3_xboole_0 @ sk_D @ sk_B))),
% 1.08/1.27      inference('sup-', [status(thm)], ['41', '44'])).
% 1.08/1.27  thf('46', plain,
% 1.08/1.27      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 1.08/1.27      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.08/1.27  thf('47', plain, ((r1_tarski @ sk_B @ sk_D)),
% 1.08/1.27      inference('sup+', [status(thm)], ['45', '46'])).
% 1.08/1.27  thf('48', plain,
% 1.08/1.27      (![X3 : $i, X5 : $i]:
% 1.08/1.27         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 1.08/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.08/1.27  thf('49', plain, ((~ (r1_tarski @ sk_D @ sk_B) | ((sk_D) = (sk_B)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['47', '48'])).
% 1.08/1.27  thf('50', plain, ((((sk_A) != (sk_C)) | ((sk_B) != (sk_D)))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('51', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 1.08/1.27      inference('split', [status(esa)], ['50'])).
% 1.08/1.27  thf('52', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.08/1.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.08/1.27  thf('53', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X1) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ X0)))),
% 1.08/1.27      inference('demod', [status(thm)], ['4', '5'])).
% 1.08/1.27  thf('54', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['52', '53'])).
% 1.08/1.27  thf('55', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.08/1.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.08/1.27  thf('56', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['52', '53'])).
% 1.08/1.27  thf('57', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 1.08/1.27         = (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['55', '56'])).
% 1.08/1.27  thf('58', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.08/1.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.27  thf('59', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 1.08/1.27         = (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('demod', [status(thm)], ['57', '58'])).
% 1.08/1.27  thf('60', plain,
% 1.08/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.08/1.27         (((X10) = (k1_xboole_0))
% 1.08/1.27          | (r1_tarski @ X11 @ X12)
% 1.08/1.27          | ~ (r1_tarski @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 1.08/1.27               (k2_zfmisc_1 @ X10 @ X12)))),
% 1.08/1.27      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.08/1.27  thf('61', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)) @ 
% 1.08/1.27             (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ X0))
% 1.08/1.27          | (r1_tarski @ sk_B @ X0)
% 1.08/1.27          | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['59', '60'])).
% 1.08/1.27  thf('62', plain,
% 1.08/1.27      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)) @ 
% 1.08/1.27           (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B))
% 1.08/1.27        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['54', '61'])).
% 1.08/1.27  thf('63', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.08/1.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.08/1.27  thf('64', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('65', plain,
% 1.08/1.27      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)) @ 
% 1.08/1.27           (k2_zfmisc_1 @ sk_C @ sk_D))
% 1.08/1.27        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.08/1.27  thf('66', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 1.08/1.27         = (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('demod', [status(thm)], ['57', '58'])).
% 1.08/1.27  thf('67', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.08/1.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.08/1.27  thf('68', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['52', '53'])).
% 1.08/1.27  thf('69', plain,
% 1.08/1.27      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ (k3_xboole_0 @ X13 @ X15) @ (k3_xboole_0 @ X14 @ X16))
% 1.08/1.27           = (k3_xboole_0 @ (k2_zfmisc_1 @ X13 @ X14) @ 
% 1.08/1.27              (k2_zfmisc_1 @ X15 @ X16)))),
% 1.08/1.27      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.08/1.27  thf('70', plain,
% 1.08/1.27      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 1.08/1.27      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.08/1.27  thf('71', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.08/1.27         (r1_tarski @ 
% 1.08/1.27          (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.08/1.27          (k2_zfmisc_1 @ X3 @ X1))),
% 1.08/1.27      inference('sup+', [status(thm)], ['69', '70'])).
% 1.08/1.27  thf('72', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B) @ 
% 1.08/1.27          (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('sup+', [status(thm)], ['68', '71'])).
% 1.08/1.27  thf('73', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B) @ 
% 1.08/1.27          (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('sup+', [status(thm)], ['67', '72'])).
% 1.08/1.27  thf('74', plain,
% 1.08/1.27      ((r1_tarski @ (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)) @ 
% 1.08/1.27        (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('sup+', [status(thm)], ['66', '73'])).
% 1.08/1.27  thf('75', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('demod', [status(thm)], ['65', '74'])).
% 1.08/1.27  thf('76', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]:
% 1.08/1.27         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.08/1.27          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['42', '43'])).
% 1.08/1.27  thf('77', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | ((sk_B) = (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['75', '76'])).
% 1.08/1.27  thf('78', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | ((sk_B) = (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['75', '76'])).
% 1.08/1.27  thf('79', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ X0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['1', '6'])).
% 1.08/1.27  thf('80', plain,
% 1.08/1.27      ((((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_B))
% 1.08/1.27          = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))
% 1.08/1.27        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['78', '79'])).
% 1.08/1.27  thf('81', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.08/1.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.08/1.27  thf('82', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 1.08/1.27         = (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 1.08/1.27      inference('demod', [status(thm)], ['57', '58'])).
% 1.08/1.27  thf('83', plain,
% 1.08/1.27      ((((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.08/1.27          = (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))
% 1.08/1.27        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.08/1.27  thf('84', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('85', plain,
% 1.08/1.27      ((((k2_zfmisc_1 @ sk_C @ sk_D)
% 1.08/1.27          = (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))
% 1.08/1.27        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('demod', [status(thm)], ['83', '84'])).
% 1.08/1.27  thf('86', plain,
% 1.08/1.27      ((((k2_zfmisc_1 @ sk_C @ sk_D) = (k2_zfmisc_1 @ sk_C @ sk_B))
% 1.08/1.27        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['77', '85'])).
% 1.08/1.27  thf('87', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | ((k2_zfmisc_1 @ sk_C @ sk_D) = (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.08/1.27      inference('simplify', [status(thm)], ['86'])).
% 1.08/1.27  thf('88', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('89', plain,
% 1.08/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.08/1.27         (((X10) = (k1_xboole_0))
% 1.08/1.27          | (r1_tarski @ X11 @ X12)
% 1.08/1.27          | ~ (r1_tarski @ (k2_zfmisc_1 @ X11 @ X10) @ 
% 1.08/1.27               (k2_zfmisc_1 @ X12 @ X10)))),
% 1.08/1.27      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.08/1.27  thf('90', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 1.08/1.27             (k2_zfmisc_1 @ X0 @ sk_B))
% 1.08/1.27          | (r1_tarski @ sk_A @ X0)
% 1.08/1.27          | ((sk_B) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['88', '89'])).
% 1.08/1.27  thf('91', plain, (((sk_B) != (k1_xboole_0))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('92', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 1.08/1.27             (k2_zfmisc_1 @ X0 @ sk_B))
% 1.08/1.27          | (r1_tarski @ sk_A @ X0))),
% 1.08/1.27      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 1.08/1.27  thf('93', plain,
% 1.08/1.27      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 1.08/1.27           (k2_zfmisc_1 @ sk_C @ sk_D))
% 1.08/1.27        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_A @ sk_C))),
% 1.08/1.27      inference('sup-', [status(thm)], ['87', '92'])).
% 1.08/1.27  thf('94', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 1.08/1.27      inference('simplify', [status(thm)], ['39'])).
% 1.08/1.27  thf('95', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_A @ sk_C))),
% 1.08/1.27      inference('demod', [status(thm)], ['93', '94'])).
% 1.08/1.27  thf('96', plain,
% 1.08/1.27      (![X3 : $i, X5 : $i]:
% 1.08/1.27         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 1.08/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.08/1.27  thf('97', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | ~ (r1_tarski @ sk_C @ sk_A)
% 1.08/1.27        | ((sk_C) = (sk_A)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['95', '96'])).
% 1.08/1.27  thf('98', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | ((k2_zfmisc_1 @ sk_C @ sk_D) = (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 1.08/1.27      inference('simplify', [status(thm)], ['86'])).
% 1.08/1.27  thf('99', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('100', plain,
% 1.08/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.08/1.27         (((X10) = (k1_xboole_0))
% 1.08/1.27          | (r1_tarski @ X11 @ X12)
% 1.08/1.27          | ~ (r1_tarski @ (k2_zfmisc_1 @ X11 @ X10) @ 
% 1.08/1.27               (k2_zfmisc_1 @ X12 @ X10)))),
% 1.08/1.27      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.08/1.27  thf('101', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 1.08/1.27             (k2_zfmisc_1 @ sk_C @ sk_D))
% 1.08/1.27          | (r1_tarski @ X0 @ sk_A)
% 1.08/1.27          | ((sk_B) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['99', '100'])).
% 1.08/1.27  thf('102', plain, (((sk_B) != (k1_xboole_0))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('103', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 1.08/1.27             (k2_zfmisc_1 @ sk_C @ sk_D))
% 1.08/1.27          | (r1_tarski @ X0 @ sk_A))),
% 1.08/1.27      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 1.08/1.27  thf('104', plain,
% 1.08/1.27      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 1.08/1.27           (k2_zfmisc_1 @ sk_C @ sk_D))
% 1.08/1.27        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_C @ sk_A))),
% 1.08/1.27      inference('sup-', [status(thm)], ['98', '103'])).
% 1.08/1.27  thf('105', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 1.08/1.27      inference('simplify', [status(thm)], ['39'])).
% 1.08/1.27  thf('106', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_C @ sk_A))),
% 1.08/1.27      inference('demod', [status(thm)], ['104', '105'])).
% 1.08/1.27  thf('107', plain,
% 1.08/1.27      ((((sk_C) = (sk_A)) | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('clc', [status(thm)], ['97', '106'])).
% 1.08/1.27  thf('108', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         ((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.08/1.27           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 1.08/1.27              (k3_xboole_0 @ sk_D @ X0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['1', '6'])).
% 1.08/1.27  thf('109', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B))
% 1.08/1.27         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 1.08/1.27      inference('demod', [status(thm)], ['8', '9'])).
% 1.08/1.27  thf('110', plain,
% 1.08/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.08/1.27         (((X10) = (k1_xboole_0))
% 1.08/1.27          | (r1_tarski @ X11 @ X12)
% 1.08/1.27          | ~ (r1_tarski @ (k2_zfmisc_1 @ X11 @ X10) @ 
% 1.08/1.27               (k2_zfmisc_1 @ X12 @ X10)))),
% 1.08/1.27      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.08/1.27  thf('111', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D) @ 
% 1.08/1.27             (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ sk_D @ sk_B)))
% 1.08/1.27          | (r1_tarski @ sk_A @ X0)
% 1.08/1.27          | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['109', '110'])).
% 1.08/1.27  thf('112', plain,
% 1.08/1.27      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D) @ 
% 1.08/1.27           (k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_B)))
% 1.08/1.27        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['108', '111'])).
% 1.08/1.27  thf('113', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.08/1.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.08/1.27  thf('114', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('115', plain,
% 1.08/1.27      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D) @ 
% 1.08/1.27           (k2_zfmisc_1 @ sk_C @ sk_D))
% 1.08/1.27        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 1.08/1.27      inference('demod', [status(thm)], ['112', '113', '114'])).
% 1.08/1.27  thf('116', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.08/1.27      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.08/1.27  thf('117', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.08/1.27         (r1_tarski @ 
% 1.08/1.27          (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.08/1.27          (k2_zfmisc_1 @ X3 @ X1))),
% 1.08/1.27      inference('sup+', [status(thm)], ['69', '70'])).
% 1.08/1.27  thf('118', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.08/1.27         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ 
% 1.08/1.27          (k2_zfmisc_1 @ X1 @ X0))),
% 1.08/1.27      inference('sup+', [status(thm)], ['116', '117'])).
% 1.08/1.27  thf('119', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))
% 1.08/1.27        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 1.08/1.27      inference('demod', [status(thm)], ['115', '118'])).
% 1.08/1.27  thf('120', plain,
% 1.08/1.27      (((r1_tarski @ sk_A @ k1_xboole_0)
% 1.08/1.27        | ((sk_C) = (sk_A))
% 1.08/1.27        | ((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['107', '119'])).
% 1.08/1.27  thf('121', plain,
% 1.08/1.27      ((((sk_C) = (sk_A)) | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('clc', [status(thm)], ['97', '106'])).
% 1.08/1.27  thf('122', plain,
% 1.08/1.27      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.08/1.27      inference('sup+', [status(thm)], ['17', '18'])).
% 1.08/1.27  thf('123', plain, (((r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_C) = (sk_A)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['121', '122'])).
% 1.08/1.27  thf('124', plain,
% 1.08/1.27      (![X3 : $i, X5 : $i]:
% 1.08/1.27         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 1.08/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.08/1.27  thf('125', plain,
% 1.08/1.27      ((((sk_C) = (sk_A))
% 1.08/1.27        | ~ (r1_tarski @ sk_A @ k1_xboole_0)
% 1.08/1.27        | ((sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['123', '124'])).
% 1.08/1.27  thf('126', plain, (((sk_A) != (k1_xboole_0))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('127', plain, ((((sk_C) = (sk_A)) | ~ (r1_tarski @ sk_A @ k1_xboole_0))),
% 1.08/1.27      inference('simplify_reflect-', [status(thm)], ['125', '126'])).
% 1.08/1.27  thf('128', plain,
% 1.08/1.27      ((((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_A)))),
% 1.08/1.27      inference('clc', [status(thm)], ['120', '127'])).
% 1.08/1.27  thf('129', plain, (((sk_B) = (k3_xboole_0 @ sk_D @ sk_B))),
% 1.08/1.27      inference('sup-', [status(thm)], ['41', '44'])).
% 1.08/1.27  thf('130', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_A)))),
% 1.08/1.27      inference('sup+', [status(thm)], ['128', '129'])).
% 1.08/1.27  thf('131', plain, (((sk_B) != (k1_xboole_0))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('132', plain, (((sk_C) = (sk_A))),
% 1.08/1.27      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 1.08/1.27  thf('133', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 1.08/1.27      inference('split', [status(esa)], ['50'])).
% 1.08/1.27  thf('134', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 1.08/1.27      inference('sup-', [status(thm)], ['132', '133'])).
% 1.08/1.27  thf('135', plain, ((((sk_A) = (sk_C)))),
% 1.08/1.27      inference('simplify', [status(thm)], ['134'])).
% 1.08/1.27  thf('136', plain, (~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C)))),
% 1.08/1.27      inference('split', [status(esa)], ['50'])).
% 1.08/1.27  thf('137', plain, (~ (((sk_B) = (sk_D)))),
% 1.08/1.27      inference('sat_resolution*', [status(thm)], ['135', '136'])).
% 1.08/1.27  thf('138', plain, (((sk_B) != (sk_D))),
% 1.08/1.27      inference('simpl_trail', [status(thm)], ['51', '137'])).
% 1.08/1.27  thf('139', plain, (~ (r1_tarski @ sk_D @ sk_B)),
% 1.08/1.27      inference('simplify_reflect-', [status(thm)], ['49', '138'])).
% 1.08/1.27  thf('140', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 1.08/1.27      inference('simplify', [status(thm)], ['39'])).
% 1.08/1.27  thf('141', plain,
% 1.08/1.27      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('142', plain,
% 1.08/1.27      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.08/1.27         (((X10) = (k1_xboole_0))
% 1.08/1.27          | (r1_tarski @ X11 @ X12)
% 1.08/1.27          | ~ (r1_tarski @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 1.08/1.27               (k2_zfmisc_1 @ X10 @ X12)))),
% 1.08/1.27      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.08/1.27  thf('143', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 1.08/1.27             (k2_zfmisc_1 @ sk_C @ sk_D))
% 1.08/1.27          | (r1_tarski @ X0 @ sk_B)
% 1.08/1.27          | ((sk_A) = (k1_xboole_0)))),
% 1.08/1.27      inference('sup-', [status(thm)], ['141', '142'])).
% 1.08/1.27  thf('144', plain, (((sk_A) != (k1_xboole_0))),
% 1.08/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.27  thf('145', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 1.08/1.27             (k2_zfmisc_1 @ sk_C @ sk_D))
% 1.08/1.27          | (r1_tarski @ X0 @ sk_B))),
% 1.08/1.27      inference('simplify_reflect-', [status(thm)], ['143', '144'])).
% 1.08/1.27  thf('146', plain, (((sk_C) = (sk_A))),
% 1.08/1.27      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 1.08/1.27  thf('147', plain,
% 1.08/1.27      (![X0 : $i]:
% 1.08/1.27         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ X0) @ 
% 1.08/1.27             (k2_zfmisc_1 @ sk_C @ sk_D))
% 1.08/1.27          | (r1_tarski @ X0 @ sk_B))),
% 1.08/1.27      inference('demod', [status(thm)], ['145', '146'])).
% 1.08/1.27  thf('148', plain, ((r1_tarski @ sk_D @ sk_B)),
% 1.08/1.27      inference('sup-', [status(thm)], ['140', '147'])).
% 1.08/1.27  thf('149', plain, ($false), inference('demod', [status(thm)], ['139', '148'])).
% 1.08/1.27  
% 1.08/1.27  % SZS output end Refutation
% 1.08/1.27  
% 1.08/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
