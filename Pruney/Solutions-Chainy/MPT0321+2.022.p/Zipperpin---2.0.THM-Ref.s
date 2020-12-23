%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GKcQQKFdat

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:35 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 796 expanded)
%              Number of leaves         :   20 ( 250 expanded)
%              Depth                    :   26
%              Number of atoms          :  920 (8657 expanded)
%              Number of equality atoms :   90 (1071 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 )
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
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

thf('6',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t122_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k3_xboole_0 @ X18 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r2_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_D ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ~ ( r2_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( r2_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X17 ) @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('34',plain,
    ( ( sk_B = sk_D )
    | ( r2_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('45',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['26','31'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_zfmisc_1 @ sk_C @ sk_D )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('55',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k3_xboole_0 @ X18 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('56',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf('60',plain,
    ( ( k2_zfmisc_1 @ sk_C @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_zfmisc_1 @ sk_C @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X13 @ X12 ) @ ( k2_zfmisc_1 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('69',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_zfmisc_1 @ sk_C @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('73',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X13 @ X12 ) @ ( k2_zfmisc_1 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('80',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_C = sk_A ),
    inference('sup+',[status(thm)],['71','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','85'])).

thf('87',plain,(
    r1_tarski @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['37','86'])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r2_xboole_0 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('89',plain,(
    ~ ( r2_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_B = sk_D ),
    inference('sup-',[status(thm)],['34','89'])).

thf('91',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,(
    sk_C = sk_A ),
    inference('sup+',[status(thm)],['71','84'])).

thf('94',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['91'])).

thf('95',plain,
    ( ( sk_C != sk_C )
   <= ( sk_A != sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    sk_A = sk_C ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['91'])).

thf('98',plain,(
    sk_B != sk_D ),
    inference('sat_resolution*',[status(thm)],['96','97'])).

thf('99',plain,(
    sk_B != sk_D ),
    inference(simpl_trail,[status(thm)],['92','98'])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GKcQQKFdat
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.09  % Solved by: fo/fo7.sh
% 0.90/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.09  % done 1315 iterations in 0.638s
% 0.90/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.09  % SZS output start Refutation
% 0.90/1.09  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.90/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.09  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.09  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.09  thf(t17_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.09  thf('0', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.90/1.09      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.90/1.09  thf(t118_zfmisc_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( r1_tarski @ A @ B ) =>
% 0.90/1.09       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.90/1.09         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.90/1.09  thf('1', plain,
% 0.90/1.09      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.09         (~ (r1_tarski @ X15 @ X16)
% 0.90/1.09          | (r1_tarski @ (k2_zfmisc_1 @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.90/1.09  thf('2', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 0.90/1.09          (k2_zfmisc_1 @ X0 @ X2))),
% 0.90/1.09      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.09  thf(d8_xboole_0, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.90/1.09       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.90/1.09  thf('3', plain,
% 0.90/1.09      (![X2 : $i, X4 : $i]:
% 0.90/1.09         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.90/1.09      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.90/1.09  thf('4', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         (((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0)
% 0.90/1.09            = (k2_zfmisc_1 @ X1 @ X0))
% 0.90/1.09          | (r2_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X2) @ X0) @ 
% 0.90/1.09             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.09  thf(idempotence_k3_xboole_0, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.90/1.09  thf('5', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.90/1.09      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.90/1.09  thf(t134_zfmisc_1, conjecture,
% 0.90/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.09     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.90/1.09       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.09         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.90/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.09    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.09        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.90/1.09          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.09            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 0.90/1.09    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 0.90/1.09  thf('6', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t122_zfmisc_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.90/1.09         ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.90/1.09       ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.09         ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.90/1.09  thf('7', plain,
% 0.90/1.09      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.09         ((k2_zfmisc_1 @ (k3_xboole_0 @ X18 @ X20) @ X19)
% 0.90/1.09           = (k3_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 0.90/1.09              (k2_zfmisc_1 @ X20 @ X19)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 0.90/1.09  thf('8', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.90/1.09           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.90/1.09              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.90/1.09      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.09  thf(t123_zfmisc_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.09     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.90/1.09       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.90/1.09  thf('9', plain,
% 0.90/1.09      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.90/1.09         ((k2_zfmisc_1 @ (k3_xboole_0 @ X22 @ X24) @ (k3_xboole_0 @ X23 @ X25))
% 0.90/1.09           = (k3_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 0.90/1.09              (k2_zfmisc_1 @ X24 @ X25)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.90/1.09  thf('10', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.90/1.09           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 0.90/1.09              (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.09  thf('11', plain,
% 0.90/1.09      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.90/1.09         ((k2_zfmisc_1 @ X21 @ (k3_xboole_0 @ X18 @ X20))
% 0.90/1.09           = (k3_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 0.90/1.09              (k2_zfmisc_1 @ X21 @ X20)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 0.90/1.09  thf('12', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.90/1.09      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.90/1.09  thf(t60_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.90/1.09  thf('13', plain,
% 0.90/1.09      (![X10 : $i, X11 : $i]:
% 0.90/1.09         (~ (r1_tarski @ X10 @ X11) | ~ (r2_xboole_0 @ X11 @ X10))),
% 0.90/1.09      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.90/1.09  thf('14', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: ~ (r2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.09      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.09  thf('15', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         ~ (r2_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 0.90/1.09            (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['11', '14'])).
% 0.90/1.09  thf('16', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ~ (r2_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_D) @ 
% 0.90/1.09            (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['10', '15'])).
% 0.90/1.09  thf('17', plain,
% 0.90/1.09      (~ (r2_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D) @ 
% 0.90/1.09          (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['5', '16'])).
% 0.90/1.09  thf('18', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('19', plain,
% 0.90/1.09      (~ (r2_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D) @ 
% 0.90/1.09          (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('demod', [status(thm)], ['17', '18'])).
% 0.90/1.09  thf('20', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D)
% 0.90/1.09         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('sup-', [status(thm)], ['4', '19'])).
% 0.90/1.09  thf(commutativity_k3_xboole_0, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.90/1.09  thf('21', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.09  thf('22', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.90/1.09      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.90/1.09  thf('23', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.90/1.09      inference('sup+', [status(thm)], ['21', '22'])).
% 0.90/1.09  thf('24', plain,
% 0.90/1.09      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.09         (~ (r1_tarski @ X15 @ X16)
% 0.90/1.09          | (r1_tarski @ (k2_zfmisc_1 @ X15 @ X17) @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.90/1.09  thf('25', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.09         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 0.90/1.09          (k2_zfmisc_1 @ X0 @ X2))),
% 0.90/1.09      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.09  thf('26', plain,
% 0.90/1.09      ((r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_D))),
% 0.90/1.09      inference('sup+', [status(thm)], ['20', '25'])).
% 0.90/1.09  thf('27', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t117_zfmisc_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.90/1.09          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.90/1.09            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.90/1.09          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.90/1.09  thf('28', plain,
% 0.90/1.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.09         (((X12) = (k1_xboole_0))
% 0.90/1.09          | (r1_tarski @ X13 @ X14)
% 0.90/1.09          | ~ (r1_tarski @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 0.90/1.09               (k2_zfmisc_1 @ X12 @ X14)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.90/1.09  thf('29', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.90/1.09             (k2_zfmisc_1 @ sk_A @ X0))
% 0.90/1.09          | (r1_tarski @ sk_B @ X0)
% 0.90/1.09          | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.09  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('31', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.90/1.09             (k2_zfmisc_1 @ sk_A @ X0))
% 0.90/1.09          | (r1_tarski @ sk_B @ X0))),
% 0.90/1.09      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.90/1.09  thf('32', plain, ((r1_tarski @ sk_B @ sk_D)),
% 0.90/1.09      inference('sup-', [status(thm)], ['26', '31'])).
% 0.90/1.09  thf('33', plain,
% 0.90/1.09      (![X2 : $i, X4 : $i]:
% 0.90/1.09         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.90/1.09      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.90/1.09  thf('34', plain, ((((sk_B) = (sk_D)) | (r2_xboole_0 @ sk_B @ sk_D))),
% 0.90/1.09      inference('sup-', [status(thm)], ['32', '33'])).
% 0.90/1.09  thf('35', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.90/1.09      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.90/1.09  thf('36', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.90/1.09      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.90/1.09  thf('37', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.90/1.09      inference('sup+', [status(thm)], ['35', '36'])).
% 0.90/1.09  thf('38', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('39', plain,
% 0.90/1.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.09         (((X12) = (k1_xboole_0))
% 0.90/1.09          | (r1_tarski @ X13 @ X14)
% 0.90/1.09          | ~ (r1_tarski @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 0.90/1.09               (k2_zfmisc_1 @ X12 @ X14)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.90/1.09  thf('40', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 0.90/1.09             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.90/1.09          | (r1_tarski @ X0 @ sk_B)
% 0.90/1.09          | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.09  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('42', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 0.90/1.09             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.90/1.09          | (r1_tarski @ X0 @ sk_B))),
% 0.90/1.09      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.90/1.09  thf('43', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.90/1.09      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.90/1.09  thf('44', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.90/1.09           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 0.90/1.09              (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.09  thf('45', plain, ((r1_tarski @ sk_B @ sk_D)),
% 0.90/1.09      inference('sup-', [status(thm)], ['26', '31'])).
% 0.90/1.09  thf(t28_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.90/1.09  thf('46', plain,
% 0.90/1.09      (![X8 : $i, X9 : $i]:
% 0.90/1.09         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.90/1.09      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.09  thf('47', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['45', '46'])).
% 0.90/1.09  thf('48', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.09  thf('49', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['47', '48'])).
% 0.90/1.09  thf('50', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.90/1.09           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X0) @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['44', '49'])).
% 0.90/1.09  thf('51', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 0.90/1.09         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 0.90/1.09      inference('sup+', [status(thm)], ['43', '50'])).
% 0.90/1.09  thf('52', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('53', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_C @ sk_D)
% 0.90/1.09         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['51', '52'])).
% 0.90/1.09  thf('54', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.90/1.09           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.90/1.09              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.90/1.09      inference('sup+', [status(thm)], ['6', '7'])).
% 0.90/1.09  thf('55', plain,
% 0.90/1.09      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.90/1.09         ((k2_zfmisc_1 @ X21 @ (k3_xboole_0 @ X18 @ X20))
% 0.90/1.09           = (k3_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 0.90/1.09              (k2_zfmisc_1 @ X21 @ X20)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 0.90/1.09  thf('56', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.90/1.09         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.90/1.09      inference('sup+', [status(thm)], ['54', '55'])).
% 0.90/1.09  thf('57', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.09  thf('58', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.90/1.09         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['56', '57'])).
% 0.90/1.09  thf('59', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['47', '48'])).
% 0.90/1.09  thf('60', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_C @ sk_B)
% 0.90/1.09         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['58', '59'])).
% 0.90/1.09  thf('61', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_C @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('sup+', [status(thm)], ['53', '60'])).
% 0.90/1.09  thf('62', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('63', plain,
% 0.90/1.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.09         (((X12) = (k1_xboole_0))
% 0.90/1.09          | (r1_tarski @ X13 @ X14)
% 0.90/1.09          | ~ (r1_tarski @ (k2_zfmisc_1 @ X13 @ X12) @ 
% 0.90/1.09               (k2_zfmisc_1 @ X14 @ X12)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.90/1.09  thf('64', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 0.90/1.09             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.90/1.09          | (r1_tarski @ X0 @ sk_A)
% 0.90/1.09          | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['62', '63'])).
% 0.90/1.09  thf('65', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('66', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 0.90/1.09             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.90/1.09          | (r1_tarski @ X0 @ sk_A))),
% 0.90/1.09      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.90/1.09  thf('67', plain,
% 0.90/1.09      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.90/1.09           (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.90/1.09        | (r1_tarski @ sk_C @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['61', '66'])).
% 0.90/1.09  thf('68', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.90/1.09      inference('sup+', [status(thm)], ['35', '36'])).
% 0.90/1.09  thf('69', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.90/1.09      inference('demod', [status(thm)], ['67', '68'])).
% 0.90/1.09  thf('70', plain,
% 0.90/1.09      (![X8 : $i, X9 : $i]:
% 0.90/1.09         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.90/1.09      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.09  thf('71', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.90/1.09      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.09  thf('72', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_C @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('sup+', [status(thm)], ['53', '60'])).
% 0.90/1.09  thf('73', plain,
% 0.90/1.09      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('74', plain,
% 0.90/1.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.09         (((X12) = (k1_xboole_0))
% 0.90/1.09          | (r1_tarski @ X13 @ X14)
% 0.90/1.09          | ~ (r1_tarski @ (k2_zfmisc_1 @ X13 @ X12) @ 
% 0.90/1.09               (k2_zfmisc_1 @ X14 @ X12)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.90/1.09  thf('75', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.90/1.09             (k2_zfmisc_1 @ X0 @ sk_B))
% 0.90/1.09          | (r1_tarski @ sk_A @ X0)
% 0.90/1.09          | ((sk_B) = (k1_xboole_0)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['73', '74'])).
% 0.90/1.09  thf('76', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('77', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.90/1.09             (k2_zfmisc_1 @ X0 @ sk_B))
% 0.90/1.09          | (r1_tarski @ sk_A @ X0))),
% 0.90/1.09      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.90/1.09  thf('78', plain,
% 0.90/1.09      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.90/1.09           (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.90/1.09        | (r1_tarski @ sk_A @ sk_C))),
% 0.90/1.09      inference('sup-', [status(thm)], ['72', '77'])).
% 0.90/1.09  thf('79', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.90/1.09      inference('sup+', [status(thm)], ['35', '36'])).
% 0.90/1.09  thf('80', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.90/1.09      inference('demod', [status(thm)], ['78', '79'])).
% 0.90/1.09  thf('81', plain,
% 0.90/1.09      (![X8 : $i, X9 : $i]:
% 0.90/1.09         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.90/1.09      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.09  thf('82', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['80', '81'])).
% 0.90/1.09  thf('83', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.09      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.09  thf('84', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['82', '83'])).
% 0.90/1.09  thf('85', plain, (((sk_C) = (sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['71', '84'])).
% 0.90/1.09  thf('86', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ X0) @ 
% 0.90/1.09             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.90/1.09          | (r1_tarski @ X0 @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['42', '85'])).
% 0.90/1.09  thf('87', plain, ((r1_tarski @ sk_D @ sk_B)),
% 0.90/1.09      inference('sup-', [status(thm)], ['37', '86'])).
% 0.90/1.09  thf('88', plain,
% 0.90/1.09      (![X10 : $i, X11 : $i]:
% 0.90/1.09         (~ (r1_tarski @ X10 @ X11) | ~ (r2_xboole_0 @ X11 @ X10))),
% 0.90/1.09      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.90/1.09  thf('89', plain, (~ (r2_xboole_0 @ sk_B @ sk_D)),
% 0.90/1.09      inference('sup-', [status(thm)], ['87', '88'])).
% 0.90/1.09  thf('90', plain, (((sk_B) = (sk_D))),
% 0.90/1.09      inference('sup-', [status(thm)], ['34', '89'])).
% 0.90/1.09  thf('91', plain, ((((sk_A) != (sk_C)) | ((sk_B) != (sk_D)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('92', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.90/1.09      inference('split', [status(esa)], ['91'])).
% 0.90/1.09  thf('93', plain, (((sk_C) = (sk_A))),
% 0.90/1.09      inference('sup+', [status(thm)], ['71', '84'])).
% 0.90/1.09  thf('94', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.90/1.09      inference('split', [status(esa)], ['91'])).
% 0.90/1.09  thf('95', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['93', '94'])).
% 0.90/1.09  thf('96', plain, ((((sk_A) = (sk_C)))),
% 0.90/1.09      inference('simplify', [status(thm)], ['95'])).
% 0.90/1.09  thf('97', plain, (~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C)))),
% 0.90/1.09      inference('split', [status(esa)], ['91'])).
% 0.90/1.09  thf('98', plain, (~ (((sk_B) = (sk_D)))),
% 0.90/1.09      inference('sat_resolution*', [status(thm)], ['96', '97'])).
% 0.90/1.09  thf('99', plain, (((sk_B) != (sk_D))),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['92', '98'])).
% 0.90/1.09  thf('100', plain, ($false),
% 0.90/1.09      inference('simplify_reflect-', [status(thm)], ['90', '99'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
