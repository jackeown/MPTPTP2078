%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0XwbZrWrT5

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:34 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 614 expanded)
%              Number of leaves         :   20 ( 193 expanded)
%              Depth                    :   27
%              Number of atoms          : 1143 (6215 expanded)
%              Number of equality atoms :  145 ( 850 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

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

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ sk_D @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_D )
      = sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,
    ( ( ( k2_xboole_0 @ sk_D @ sk_B )
      = sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k2_xboole_0 @ X18 @ X20 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_C @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('45',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('49',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('53',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_D )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_D )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('64',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_tarski @ sk_D @ sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B @ sk_D )
    | ( sk_B = sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,
    ( ( sk_B = sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_A != sk_C )
    | ( sk_B = sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('78',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k2_xboole_0 @ X18 @ X20 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('86',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_A )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('90',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('91',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('92',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('93',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('95',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('97',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('99',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['90','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('102',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('104',plain,(
    r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('106',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,
    ( ( k2_zfmisc_1 @ sk_C @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['89','108'])).

thf('110',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('117',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    sk_C = sk_A ),
    inference(demod,[status(thm)],['88','117'])).

thf('119',plain,
    ( ( sk_C != sk_C )
    | ( sk_B = sk_D ) ),
    inference(demod,[status(thm)],['75','118'])).

thf('120',plain,(
    sk_B = sk_D ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['121'])).

thf('123',plain,(
    sk_C = sk_A ),
    inference(demod,[status(thm)],['88','117'])).

thf('124',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['121'])).

thf('125',plain,
    ( ( sk_C != sk_C )
   <= ( sk_A != sk_C ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    sk_A = sk_C ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['121'])).

thf('128',plain,(
    sk_B != sk_D ),
    inference('sat_resolution*',[status(thm)],['126','127'])).

thf('129',plain,(
    sk_B != sk_D ),
    inference(simpl_trail,[status(thm)],['122','128'])).

thf('130',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['120','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0XwbZrWrT5
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.81  % Solved by: fo/fo7.sh
% 0.58/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.81  % done 670 iterations in 0.356s
% 0.58/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.81  % SZS output start Refutation
% 0.58/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.81  thf(d10_xboole_0, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.81  thf('0', plain,
% 0.58/0.81      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.58/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.81  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.58/0.81      inference('simplify', [status(thm)], ['0'])).
% 0.58/0.81  thf(commutativity_k2_xboole_0, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.58/0.81  thf('2', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.81  thf(t21_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.58/0.81  thf('3', plain,
% 0.58/0.81      (![X11 : $i, X12 : $i]:
% 0.58/0.81         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 0.58/0.81      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.58/0.81  thf('4', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['2', '3'])).
% 0.58/0.81  thf(t134_zfmisc_1, conjecture,
% 0.58/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.58/0.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.81         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.58/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.81    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.58/0.81          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.81            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 0.58/0.81    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 0.58/0.81  thf('5', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(t120_zfmisc_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.58/0.81         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.58/0.81       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.81         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.58/0.81  thf('6', plain,
% 0.58/0.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.58/0.81         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 0.58/0.81           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 0.58/0.81              (k2_zfmisc_1 @ X20 @ X19)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.58/0.81  thf('7', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.58/0.81           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.81  thf('8', plain,
% 0.58/0.81      (![X11 : $i, X12 : $i]:
% 0.58/0.81         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 0.58/0.81      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.58/0.81  thf('9', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))
% 0.58/0.81           = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('sup+', [status(thm)], ['7', '8'])).
% 0.58/0.81  thf(t123_zfmisc_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.58/0.81       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.58/0.81  thf('10', plain,
% 0.58/0.81      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.58/0.81         ((k2_zfmisc_1 @ (k3_xboole_0 @ X22 @ X24) @ (k3_xboole_0 @ X23 @ X25))
% 0.58/0.81           = (k3_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 0.58/0.81              (k2_zfmisc_1 @ X24 @ X25)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.58/0.81  thf('11', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 0.58/0.81           (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.81  thf('12', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.58/0.81         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('sup+', [status(thm)], ['4', '11'])).
% 0.58/0.81  thf(t117_zfmisc_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.81          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.58/0.81            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.58/0.81          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.58/0.81  thf('13', plain,
% 0.58/0.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.81         (((X15) = (k1_xboole_0))
% 0.58/0.81          | (r1_tarski @ X16 @ X17)
% 0.58/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 0.58/0.81               (k2_zfmisc_1 @ X15 @ X17)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.58/0.81  thf('14', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ X0) @ 
% 0.58/0.81             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.58/0.81          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.58/0.81          | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf('15', plain,
% 0.58/0.81      ((((sk_C) = (k1_xboole_0))
% 0.58/0.81        | (r1_tarski @ sk_D @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['1', '14'])).
% 0.58/0.81  thf(t17_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.81  thf('16', plain,
% 0.58/0.81      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.58/0.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.58/0.81  thf('17', plain,
% 0.58/0.81      (![X4 : $i, X6 : $i]:
% 0.58/0.81         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.58/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.81  thf('18', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.58/0.81          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.81  thf('19', plain,
% 0.58/0.81      ((((sk_C) = (k1_xboole_0)) | ((sk_D) = (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['15', '18'])).
% 0.58/0.81  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.81  thf('20', plain,
% 0.58/0.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.81  thf('21', plain,
% 0.58/0.81      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.58/0.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.58/0.81  thf(t12_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.58/0.81  thf('22', plain,
% 0.58/0.81      (![X7 : $i, X8 : $i]:
% 0.58/0.81         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.81  thf('23', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.81  thf('24', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.81  thf('25', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.58/0.81      inference('demod', [status(thm)], ['23', '24'])).
% 0.58/0.81  thf('26', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['20', '25'])).
% 0.58/0.81  thf('27', plain,
% 0.58/0.81      ((((k2_xboole_0 @ sk_B @ sk_D) = (sk_B)) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['19', '26'])).
% 0.58/0.81  thf('28', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.81  thf('29', plain,
% 0.58/0.81      ((((k2_xboole_0 @ sk_D @ sk_B) = (sk_B)) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['27', '28'])).
% 0.58/0.81  thf('30', plain,
% 0.58/0.81      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.58/0.81         ((k2_zfmisc_1 @ X21 @ (k2_xboole_0 @ X18 @ X20))
% 0.58/0.81           = (k2_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 0.58/0.81              (k2_zfmisc_1 @ X21 @ X20)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.58/0.81  thf(t7_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.81  thf('31', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.81  thf('32', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (r1_tarski @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 0.58/0.81          (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['30', '31'])).
% 0.58/0.81  thf('33', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D) @ (k2_zfmisc_1 @ X0 @ sk_B))
% 0.58/0.81          | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['29', '32'])).
% 0.58/0.81  thf('34', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('35', plain,
% 0.58/0.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.81         (((X15) = (k1_xboole_0))
% 0.58/0.81          | (r1_tarski @ X16 @ X17)
% 0.58/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X16 @ X15) @ 
% 0.58/0.81               (k2_zfmisc_1 @ X17 @ X15)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.58/0.81  thf('36', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81             (k2_zfmisc_1 @ X0 @ sk_B))
% 0.58/0.81          | (r1_tarski @ sk_A @ X0)
% 0.58/0.81          | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.81  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('38', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81             (k2_zfmisc_1 @ X0 @ sk_B))
% 0.58/0.81          | (r1_tarski @ sk_A @ X0))),
% 0.58/0.81      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.58/0.81  thf('39', plain, ((((sk_C) = (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_C))),
% 0.58/0.81      inference('sup-', [status(thm)], ['33', '38'])).
% 0.58/0.81  thf('40', plain,
% 0.58/0.81      (![X7 : $i, X8 : $i]:
% 0.58/0.81         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.81  thf('41', plain,
% 0.58/0.81      ((((sk_C) = (k1_xboole_0)) | ((k2_xboole_0 @ sk_A @ sk_C) = (sk_C)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.58/0.81  thf('42', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.81  thf('43', plain,
% 0.58/0.81      ((((sk_C) = (k1_xboole_0)) | ((k2_xboole_0 @ sk_C @ sk_A) = (sk_C)))),
% 0.58/0.81      inference('demod', [status(thm)], ['41', '42'])).
% 0.58/0.81  thf('44', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['2', '3'])).
% 0.58/0.81  thf('45', plain,
% 0.58/0.81      ((((k3_xboole_0 @ sk_A @ sk_C) = (sk_A)) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['43', '44'])).
% 0.58/0.81  thf('46', plain,
% 0.58/0.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.81  thf('47', plain,
% 0.58/0.81      ((((k3_xboole_0 @ sk_C @ sk_A) = (sk_A)) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['45', '46'])).
% 0.58/0.81  thf('48', plain,
% 0.58/0.81      ((((sk_C) = (k1_xboole_0)) | ((sk_D) = (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['15', '18'])).
% 0.58/0.81  thf('49', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.58/0.81      inference('simplify', [status(thm)], ['0'])).
% 0.58/0.81  thf('50', plain,
% 0.58/0.81      (![X7 : $i, X8 : $i]:
% 0.58/0.81         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.81  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['49', '50'])).
% 0.58/0.81  thf('52', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 0.58/0.81           (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.81  thf('53', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.58/0.81         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('sup+', [status(thm)], ['51', '52'])).
% 0.58/0.81  thf('54', plain,
% 0.58/0.81      ((((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D)
% 0.58/0.81          = (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.58/0.81        | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['48', '53'])).
% 0.58/0.81  thf('55', plain,
% 0.58/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_D) = (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.58/0.81        | ((sk_C) = (k1_xboole_0))
% 0.58/0.81        | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['47', '54'])).
% 0.58/0.81  thf('56', plain,
% 0.58/0.81      ((((sk_C) = (k1_xboole_0))
% 0.58/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_D) = (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['55'])).
% 0.58/0.81  thf('57', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('58', plain,
% 0.58/0.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.81         (((X15) = (k1_xboole_0))
% 0.58/0.81          | (r1_tarski @ X16 @ X17)
% 0.58/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 0.58/0.81               (k2_zfmisc_1 @ X15 @ X17)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.58/0.81  thf('59', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81             (k2_zfmisc_1 @ sk_A @ X0))
% 0.58/0.81          | (r1_tarski @ sk_B @ X0)
% 0.58/0.81          | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['57', '58'])).
% 0.58/0.81  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('61', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81             (k2_zfmisc_1 @ sk_A @ X0))
% 0.58/0.81          | (r1_tarski @ sk_B @ X0))),
% 0.58/0.81      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.58/0.81  thf('62', plain,
% 0.58/0.81      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81           (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.58/0.81        | ((sk_C) = (k1_xboole_0))
% 0.58/0.81        | (r1_tarski @ sk_B @ sk_D))),
% 0.58/0.81      inference('sup-', [status(thm)], ['56', '61'])).
% 0.58/0.81  thf('63', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.58/0.81      inference('simplify', [status(thm)], ['0'])).
% 0.58/0.81  thf('64', plain, ((((sk_C) = (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_D))),
% 0.58/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.58/0.81  thf('65', plain,
% 0.58/0.81      ((((sk_C) = (k1_xboole_0)) | ((sk_D) = (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['15', '18'])).
% 0.58/0.81  thf('66', plain,
% 0.58/0.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.81  thf('67', plain,
% 0.58/0.81      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.58/0.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.58/0.81  thf('68', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.58/0.81      inference('sup+', [status(thm)], ['66', '67'])).
% 0.58/0.81  thf('69', plain, (((r1_tarski @ sk_D @ sk_B) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['65', '68'])).
% 0.58/0.81  thf('70', plain,
% 0.58/0.81      (![X4 : $i, X6 : $i]:
% 0.58/0.81         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.58/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.81  thf('71', plain,
% 0.58/0.81      ((((sk_C) = (k1_xboole_0))
% 0.58/0.81        | ~ (r1_tarski @ sk_B @ sk_D)
% 0.58/0.81        | ((sk_B) = (sk_D)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['69', '70'])).
% 0.58/0.81  thf('72', plain,
% 0.58/0.81      ((((sk_C) = (k1_xboole_0)) | ((sk_B) = (sk_D)) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['64', '71'])).
% 0.58/0.81  thf('73', plain, ((((sk_B) = (sk_D)) | ((sk_C) = (k1_xboole_0)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['72'])).
% 0.58/0.81  thf('74', plain, (((sk_A) != (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('75', plain, ((((sk_A) != (sk_C)) | ((sk_B) = (sk_D)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['73', '74'])).
% 0.58/0.81  thf('76', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.58/0.81         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('sup+', [status(thm)], ['4', '11'])).
% 0.58/0.81  thf('77', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['20', '25'])).
% 0.58/0.81  thf('78', plain,
% 0.58/0.81      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.58/0.81         ((k2_zfmisc_1 @ X21 @ (k2_xboole_0 @ X18 @ X20))
% 0.58/0.81           = (k2_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 0.58/0.81              (k2_zfmisc_1 @ X21 @ X20)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.58/0.81  thf('79', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.81  thf('80', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.58/0.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.81  thf('81', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['79', '80'])).
% 0.58/0.81  thf('82', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (r1_tarski @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.58/0.81          (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['78', '81'])).
% 0.58/0.81  thf('83', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.58/0.81          (k2_zfmisc_1 @ X2 @ X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['77', '82'])).
% 0.58/0.81  thf('84', plain,
% 0.58/0.81      ((r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ (k2_zfmisc_1 @ sk_C @ sk_B))),
% 0.58/0.81      inference('sup+', [status(thm)], ['76', '83'])).
% 0.58/0.81  thf('85', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81             (k2_zfmisc_1 @ X0 @ sk_B))
% 0.58/0.81          | (r1_tarski @ sk_A @ X0))),
% 0.58/0.81      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.58/0.81  thf('86', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.58/0.81      inference('sup-', [status(thm)], ['84', '85'])).
% 0.58/0.81  thf('87', plain,
% 0.58/0.81      (![X4 : $i, X6 : $i]:
% 0.58/0.81         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.58/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.81  thf('88', plain, ((~ (r1_tarski @ sk_C @ sk_A) | ((sk_C) = (sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['86', '87'])).
% 0.58/0.81  thf('89', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.58/0.81         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('sup+', [status(thm)], ['4', '11'])).
% 0.58/0.81  thf('90', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.58/0.81         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('sup+', [status(thm)], ['51', '52'])).
% 0.58/0.81  thf('91', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.58/0.81      inference('sup-', [status(thm)], ['84', '85'])).
% 0.58/0.81  thf('92', plain,
% 0.58/0.81      (![X7 : $i, X8 : $i]:
% 0.58/0.81         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.81  thf('93', plain, (((k2_xboole_0 @ sk_A @ sk_C) = (sk_C))),
% 0.58/0.81      inference('sup-', [status(thm)], ['91', '92'])).
% 0.58/0.81  thf('94', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.81  thf('95', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.58/0.81      inference('demod', [status(thm)], ['93', '94'])).
% 0.58/0.81  thf('96', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['2', '3'])).
% 0.58/0.81  thf('97', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.58/0.81      inference('sup+', [status(thm)], ['95', '96'])).
% 0.58/0.81  thf('98', plain,
% 0.58/0.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.58/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.81  thf('99', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['97', '98'])).
% 0.58/0.81  thf('100', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.58/0.81         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('demod', [status(thm)], ['90', '99'])).
% 0.58/0.81  thf('101', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81             (k2_zfmisc_1 @ sk_A @ X0))
% 0.58/0.81          | (r1_tarski @ sk_B @ X0))),
% 0.58/0.81      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.58/0.81  thf('102', plain,
% 0.58/0.81      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81           (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.58/0.81        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['100', '101'])).
% 0.58/0.81  thf('103', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.58/0.81      inference('simplify', [status(thm)], ['0'])).
% 0.58/0.81  thf('104', plain, ((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_D @ sk_B))),
% 0.58/0.81      inference('demod', [status(thm)], ['102', '103'])).
% 0.58/0.81  thf('105', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.58/0.81      inference('sup+', [status(thm)], ['66', '67'])).
% 0.58/0.81  thf('106', plain,
% 0.58/0.81      (![X4 : $i, X6 : $i]:
% 0.58/0.81         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.58/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.81  thf('107', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.81          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.81  thf('108', plain, (((sk_B) = (k3_xboole_0 @ sk_D @ sk_B))),
% 0.58/0.81      inference('sup-', [status(thm)], ['104', '107'])).
% 0.58/0.81  thf('109', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ sk_C @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('demod', [status(thm)], ['89', '108'])).
% 0.58/0.81  thf('110', plain,
% 0.58/0.81      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('111', plain,
% 0.58/0.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.81         (((X15) = (k1_xboole_0))
% 0.58/0.81          | (r1_tarski @ X16 @ X17)
% 0.58/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X16 @ X15) @ 
% 0.58/0.81               (k2_zfmisc_1 @ X17 @ X15)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.58/0.81  thf('112', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 0.58/0.81             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.58/0.81          | (r1_tarski @ X0 @ sk_A)
% 0.58/0.81          | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['110', '111'])).
% 0.58/0.81  thf('113', plain, (((sk_B) != (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('114', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 0.58/0.81             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.58/0.81          | (r1_tarski @ X0 @ sk_A))),
% 0.58/0.81      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 0.58/0.81  thf('115', plain,
% 0.58/0.81      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.58/0.81           (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.58/0.81        | (r1_tarski @ sk_C @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['109', '114'])).
% 0.58/0.81  thf('116', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.58/0.81      inference('simplify', [status(thm)], ['0'])).
% 0.58/0.81  thf('117', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.58/0.81      inference('demod', [status(thm)], ['115', '116'])).
% 0.58/0.81  thf('118', plain, (((sk_C) = (sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['88', '117'])).
% 0.58/0.81  thf('119', plain, ((((sk_C) != (sk_C)) | ((sk_B) = (sk_D)))),
% 0.58/0.81      inference('demod', [status(thm)], ['75', '118'])).
% 0.58/0.81  thf('120', plain, (((sk_B) = (sk_D))),
% 0.58/0.81      inference('simplify', [status(thm)], ['119'])).
% 0.58/0.81  thf('121', plain, ((((sk_A) != (sk_C)) | ((sk_B) != (sk_D)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('122', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.58/0.81      inference('split', [status(esa)], ['121'])).
% 0.58/0.81  thf('123', plain, (((sk_C) = (sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['88', '117'])).
% 0.58/0.81  thf('124', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.58/0.81      inference('split', [status(esa)], ['121'])).
% 0.58/0.81  thf('125', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['123', '124'])).
% 0.58/0.81  thf('126', plain, ((((sk_A) = (sk_C)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['125'])).
% 0.58/0.81  thf('127', plain, (~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C)))),
% 0.58/0.81      inference('split', [status(esa)], ['121'])).
% 0.58/0.81  thf('128', plain, (~ (((sk_B) = (sk_D)))),
% 0.58/0.81      inference('sat_resolution*', [status(thm)], ['126', '127'])).
% 0.58/0.81  thf('129', plain, (((sk_B) != (sk_D))),
% 0.58/0.81      inference('simpl_trail', [status(thm)], ['122', '128'])).
% 0.58/0.81  thf('130', plain, ($false),
% 0.58/0.81      inference('simplify_reflect-', [status(thm)], ['120', '129'])).
% 0.58/0.81  
% 0.58/0.81  % SZS output end Refutation
% 0.58/0.81  
% 0.58/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
