%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sWLsQm7ezr

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:33 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  183 (1414 expanded)
%              Number of leaves         :   21 ( 456 expanded)
%              Depth                    :   26
%              Number of atoms          : 1511 (15156 expanded)
%              Number of equality atoms :  170 (1855 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','5'])).

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

thf('7',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X43 @ X45 ) @ X44 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('17',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r1_tarski @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X40 @ X41 ) @ ( k2_zfmisc_1 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_D_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('21',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_D_1 )
      = sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,
    ( ( ( k2_xboole_0 @ sk_D_1 @ sk_B_1 )
      = sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('35',plain,(
    ! [X43: $i,X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ X46 @ ( k2_xboole_0 @ X43 @ X45 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X46 @ X43 ) @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('36',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r1_tarski @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X41 @ X40 ) @ ( k2_zfmisc_1 @ X42 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('55',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('57',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D_1 )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_D_1 )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_D_1 )
      = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r1_tarski @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X40 @ X41 ) @ ( k2_zfmisc_1 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('68',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D_1 )
    | ( sk_B_1 = sk_D_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = sk_D_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( sk_B_1 = sk_D_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 = sk_D_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B_1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B_1 @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ X1 ) @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('86',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) @ ( k3_xboole_0 @ X0 @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_C_1 ) @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('92',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('95',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf('97',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('99',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('101',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_A )
    | ( sk_C_1
      = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('109',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('110',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_A )
    | ( sk_C_1 = sk_A ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('112',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('116',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['113','118'])).

thf('120',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('125',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('126',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['112','127'])).

thf('129',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('130',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('131',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('134',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('136',plain,(
    r1_tarski @ sk_B_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('138',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_D_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['111','138'])).

thf('140',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r1_tarski @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X41 @ X40 ) @ ( k2_zfmisc_1 @ X42 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('147',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    sk_C_1 = sk_A ),
    inference(demod,[status(thm)],['110','147'])).

thf('149',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( sk_B_1 = sk_D_1 ) ),
    inference(demod,[status(thm)],['79','148'])).

thf('150',plain,(
    sk_B_1 = sk_D_1 ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( sk_B_1 != sk_D_1 )
   <= ( sk_B_1 != sk_D_1 ) ),
    inference(split,[status(esa)],['151'])).

thf('153',plain,(
    sk_C_1 = sk_A ),
    inference(demod,[status(thm)],['110','147'])).

thf('154',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['151'])).

thf('155',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    sk_A = sk_C_1 ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( sk_B_1 != sk_D_1 )
    | ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['151'])).

thf('158',plain,(
    sk_B_1 != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['156','157'])).

thf('159',plain,(
    sk_B_1 != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['152','158'])).

thf('160',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['150','159'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sWLsQm7ezr
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.06/2.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.06/2.28  % Solved by: fo/fo7.sh
% 2.06/2.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.06/2.28  % done 3316 iterations in 1.822s
% 2.06/2.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.06/2.28  % SZS output start Refutation
% 2.06/2.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.06/2.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.06/2.28  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.06/2.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.06/2.28  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.06/2.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.06/2.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.06/2.28  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.06/2.28  thf(sk_A_type, type, sk_A: $i).
% 2.06/2.28  thf(d10_xboole_0, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.06/2.28  thf('0', plain,
% 2.06/2.28      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 2.06/2.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.06/2.28  thf('1', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 2.06/2.28      inference('simplify', [status(thm)], ['0'])).
% 2.06/2.28  thf(commutativity_k2_xboole_0, axiom,
% 2.06/2.28    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.06/2.28  thf('2', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.06/2.28  thf(t7_xboole_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.06/2.28  thf('3', plain,
% 2.06/2.28      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.06/2.28      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.06/2.28  thf(t28_xboole_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.06/2.28  thf('4', plain,
% 2.06/2.28      (![X20 : $i, X21 : $i]:
% 2.06/2.28         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 2.06/2.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.06/2.28  thf('5', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 2.06/2.28      inference('sup-', [status(thm)], ['3', '4'])).
% 2.06/2.28  thf('6', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 2.06/2.28      inference('sup+', [status(thm)], ['2', '5'])).
% 2.06/2.28  thf(t134_zfmisc_1, conjecture,
% 2.06/2.28    (![A:$i,B:$i,C:$i,D:$i]:
% 2.06/2.28     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.06/2.28       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.06/2.28         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 2.06/2.28  thf(zf_stmt_0, negated_conjecture,
% 2.06/2.28    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.06/2.28        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.06/2.28          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.06/2.28            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 2.06/2.28    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 2.06/2.28  thf('7', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf(t120_zfmisc_1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i]:
% 2.06/2.28     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 2.06/2.28         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 2.06/2.28       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.06/2.28         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 2.06/2.28  thf('8', plain,
% 2.06/2.28      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k2_xboole_0 @ X43 @ X45) @ X44)
% 2.06/2.28           = (k2_xboole_0 @ (k2_zfmisc_1 @ X43 @ X44) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X45 @ X44)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 2.06/2.28  thf('9', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 2.06/2.28           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['7', '8'])).
% 2.06/2.28  thf('10', plain,
% 2.06/2.28      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.06/2.28      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.06/2.28  thf('11', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['9', '10'])).
% 2.06/2.28  thf('12', plain,
% 2.06/2.28      (![X20 : $i, X21 : $i]:
% 2.06/2.28         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 2.06/2.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.06/2.28  thf('13', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1))
% 2.06/2.28           = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('sup-', [status(thm)], ['11', '12'])).
% 2.06/2.28  thf(t123_zfmisc_1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i,D:$i]:
% 2.06/2.28     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 2.06/2.28       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 2.06/2.28  thf('14', plain,
% 2.06/2.28      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.06/2.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.06/2.28  thf('15', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 2.06/2.28           (k3_xboole_0 @ sk_D_1 @ sk_B_1)) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['13', '14'])).
% 2.06/2.28  thf('16', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28         = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['6', '15'])).
% 2.06/2.28  thf(t117_zfmisc_1, axiom,
% 2.06/2.28    (![A:$i,B:$i,C:$i]:
% 2.06/2.28     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.06/2.28          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 2.06/2.28            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 2.06/2.28          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 2.06/2.28  thf('17', plain,
% 2.06/2.28      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.06/2.28         (((X40) = (k1_xboole_0))
% 2.06/2.28          | (r1_tarski @ X41 @ X42)
% 2.06/2.28          | ~ (r1_tarski @ (k2_zfmisc_1 @ X40 @ X41) @ 
% 2.06/2.28               (k2_zfmisc_1 @ X40 @ X42)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.06/2.28  thf('18', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ X0) @ 
% 2.06/2.28             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28          | ((sk_C_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['16', '17'])).
% 2.06/2.28  thf('19', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0))
% 2.06/2.28        | (r1_tarski @ sk_D_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['1', '18'])).
% 2.06/2.28  thf(t17_xboole_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.06/2.28  thf('20', plain,
% 2.06/2.28      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 2.06/2.28      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.06/2.28  thf('21', plain,
% 2.06/2.28      (![X13 : $i, X15 : $i]:
% 2.06/2.28         (((X13) = (X15))
% 2.06/2.28          | ~ (r1_tarski @ X15 @ X13)
% 2.06/2.28          | ~ (r1_tarski @ X13 @ X15))),
% 2.06/2.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.06/2.28  thf('22', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.06/2.28          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['20', '21'])).
% 2.06/2.28  thf('23', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0))
% 2.06/2.28        | ((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['19', '22'])).
% 2.06/2.28  thf(commutativity_k3_xboole_0, axiom,
% 2.06/2.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.06/2.28  thf('24', plain,
% 2.06/2.28      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.06/2.28  thf('25', plain,
% 2.06/2.28      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 2.06/2.28      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.06/2.28  thf(t12_xboole_1, axiom,
% 2.06/2.28    (![A:$i,B:$i]:
% 2.06/2.28     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.06/2.28  thf('26', plain,
% 2.06/2.28      (![X16 : $i, X17 : $i]:
% 2.06/2.28         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 2.06/2.28      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.06/2.28  thf('27', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.06/2.28      inference('sup-', [status(thm)], ['25', '26'])).
% 2.06/2.28  thf('28', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.06/2.28  thf('29', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 2.06/2.28      inference('demod', [status(thm)], ['27', '28'])).
% 2.06/2.28  thf('30', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 2.06/2.28      inference('sup+', [status(thm)], ['24', '29'])).
% 2.06/2.28  thf('31', plain,
% 2.06/2.28      ((((k2_xboole_0 @ sk_B_1 @ sk_D_1) = (sk_B_1))
% 2.06/2.28        | ((sk_C_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['23', '30'])).
% 2.06/2.28  thf('32', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.06/2.28  thf('33', plain,
% 2.06/2.28      ((((k2_xboole_0 @ sk_D_1 @ sk_B_1) = (sk_B_1))
% 2.06/2.28        | ((sk_C_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('demod', [status(thm)], ['31', '32'])).
% 2.06/2.28  thf('34', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 2.06/2.28           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['7', '8'])).
% 2.06/2.28  thf('35', plain,
% 2.06/2.28      (![X43 : $i, X45 : $i, X46 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ X46 @ (k2_xboole_0 @ X43 @ X45))
% 2.06/2.28           = (k2_xboole_0 @ (k2_zfmisc_1 @ X46 @ X43) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X46 @ X45)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 2.06/2.28  thf('36', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['34', '35'])).
% 2.06/2.28  thf('37', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.06/2.28  thf('38', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['36', '37'])).
% 2.06/2.28  thf('39', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.06/2.28  thf('40', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['9', '10'])).
% 2.06/2.28  thf('41', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28          (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['39', '40'])).
% 2.06/2.28  thf('42', plain,
% 2.06/2.28      ((r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28        (k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['38', '41'])).
% 2.06/2.28  thf('43', plain,
% 2.06/2.28      (((r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28         (k2_zfmisc_1 @ sk_C_1 @ sk_B_1))
% 2.06/2.28        | ((sk_C_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['33', '42'])).
% 2.06/2.28  thf('44', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('45', plain,
% 2.06/2.28      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.06/2.28         (((X40) = (k1_xboole_0))
% 2.06/2.28          | (r1_tarski @ X41 @ X42)
% 2.06/2.28          | ~ (r1_tarski @ (k2_zfmisc_1 @ X41 @ X40) @ 
% 2.06/2.28               (k2_zfmisc_1 @ X42 @ X40)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.06/2.28  thf('46', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28             (k2_zfmisc_1 @ X0 @ sk_B_1))
% 2.06/2.28          | (r1_tarski @ sk_A @ X0)
% 2.06/2.28          | ((sk_B_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['44', '45'])).
% 2.06/2.28  thf('47', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('48', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28             (k2_zfmisc_1 @ X0 @ sk_B_1))
% 2.06/2.28          | (r1_tarski @ sk_A @ X0))),
% 2.06/2.28      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 2.06/2.28  thf('49', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_C_1))),
% 2.06/2.28      inference('sup-', [status(thm)], ['43', '48'])).
% 2.06/2.28  thf('50', plain,
% 2.06/2.28      (![X20 : $i, X21 : $i]:
% 2.06/2.28         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 2.06/2.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.06/2.28  thf('51', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0)) | ((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['49', '50'])).
% 2.06/2.28  thf('52', plain,
% 2.06/2.28      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.06/2.28  thf('53', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0)) | ((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_A)))),
% 2.06/2.28      inference('demod', [status(thm)], ['51', '52'])).
% 2.06/2.28  thf('54', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0))
% 2.06/2.28        | ((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['19', '22'])).
% 2.06/2.28  thf(idempotence_k2_xboole_0, axiom,
% 2.06/2.28    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.06/2.28  thf('55', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 2.06/2.28      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.06/2.28  thf('56', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 2.06/2.28           (k3_xboole_0 @ sk_D_1 @ sk_B_1)) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['13', '14'])).
% 2.06/2.28  thf('57', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 2.06/2.28         (k3_xboole_0 @ sk_D_1 @ sk_B_1)) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['55', '56'])).
% 2.06/2.28  thf('58', plain,
% 2.06/2.28      ((((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_D_1)
% 2.06/2.28          = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28        | ((sk_C_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['54', '57'])).
% 2.06/2.28  thf('59', plain,
% 2.06/2.28      ((((k2_zfmisc_1 @ sk_A @ sk_D_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28        | ((sk_C_1) = (k1_xboole_0))
% 2.06/2.28        | ((sk_C_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['53', '58'])).
% 2.06/2.28  thf('60', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0))
% 2.06/2.28        | ((k2_zfmisc_1 @ sk_A @ sk_D_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)))),
% 2.06/2.28      inference('simplify', [status(thm)], ['59'])).
% 2.06/2.28  thf('61', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('62', plain,
% 2.06/2.28      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.06/2.28         (((X40) = (k1_xboole_0))
% 2.06/2.28          | (r1_tarski @ X41 @ X42)
% 2.06/2.28          | ~ (r1_tarski @ (k2_zfmisc_1 @ X40 @ X41) @ 
% 2.06/2.28               (k2_zfmisc_1 @ X40 @ X42)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.06/2.28  thf('63', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28             (k2_zfmisc_1 @ sk_A @ X0))
% 2.06/2.28          | (r1_tarski @ sk_B_1 @ X0)
% 2.06/2.28          | ((sk_A) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['61', '62'])).
% 2.06/2.28  thf('64', plain, (((sk_A) != (k1_xboole_0))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('65', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28             (k2_zfmisc_1 @ sk_A @ X0))
% 2.06/2.28          | (r1_tarski @ sk_B_1 @ X0))),
% 2.06/2.28      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 2.06/2.28  thf('66', plain,
% 2.06/2.28      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28           (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28        | ((sk_C_1) = (k1_xboole_0))
% 2.06/2.28        | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 2.06/2.28      inference('sup-', [status(thm)], ['60', '65'])).
% 2.06/2.28  thf('67', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 2.06/2.28      inference('simplify', [status(thm)], ['0'])).
% 2.06/2.28  thf('68', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_D_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['66', '67'])).
% 2.06/2.28  thf('69', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0))
% 2.06/2.28        | ((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['19', '22'])).
% 2.06/2.28  thf('70', plain,
% 2.06/2.28      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.06/2.28  thf('71', plain,
% 2.06/2.28      (![X18 : $i, X19 : $i]: (r1_tarski @ (k3_xboole_0 @ X18 @ X19) @ X18)),
% 2.06/2.28      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.06/2.28  thf('72', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.06/2.28      inference('sup+', [status(thm)], ['70', '71'])).
% 2.06/2.28  thf('73', plain,
% 2.06/2.28      (((r1_tarski @ sk_D_1 @ sk_B_1) | ((sk_C_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['69', '72'])).
% 2.06/2.28  thf('74', plain,
% 2.06/2.28      (![X13 : $i, X15 : $i]:
% 2.06/2.28         (((X13) = (X15))
% 2.06/2.28          | ~ (r1_tarski @ X15 @ X13)
% 2.06/2.28          | ~ (r1_tarski @ X13 @ X15))),
% 2.06/2.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.06/2.28  thf('75', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0))
% 2.06/2.28        | ~ (r1_tarski @ sk_B_1 @ sk_D_1)
% 2.06/2.28        | ((sk_B_1) = (sk_D_1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['73', '74'])).
% 2.06/2.28  thf('76', plain,
% 2.06/2.28      ((((sk_C_1) = (k1_xboole_0))
% 2.06/2.28        | ((sk_B_1) = (sk_D_1))
% 2.06/2.28        | ((sk_C_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['68', '75'])).
% 2.06/2.28  thf('77', plain, ((((sk_B_1) = (sk_D_1)) | ((sk_C_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('simplify', [status(thm)], ['76'])).
% 2.06/2.28  thf('78', plain, (((sk_A) != (k1_xboole_0))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('79', plain, ((((sk_A) != (sk_C_1)) | ((sk_B_1) = (sk_D_1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['77', '78'])).
% 2.06/2.28  thf('80', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('81', plain,
% 2.06/2.28      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.06/2.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.06/2.28  thf('82', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ 
% 2.06/2.28           (k3_xboole_0 @ sk_B_1 @ X0))
% 2.06/2.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X1 @ X0)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['80', '81'])).
% 2.06/2.28  thf('83', plain,
% 2.06/2.28      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.06/2.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.06/2.28  thf('84', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ 
% 2.06/2.28           (k3_xboole_0 @ sk_B_1 @ X0))
% 2.06/2.28           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ X1) @ 
% 2.06/2.28              (k3_xboole_0 @ sk_D_1 @ X0)))),
% 2.06/2.28      inference('demod', [status(thm)], ['82', '83'])).
% 2.06/2.28  thf('85', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['36', '37'])).
% 2.06/2.28  thf('86', plain,
% 2.06/2.28      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.06/2.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.06/2.28  thf('87', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ sk_C_1 @ sk_A)) @ 
% 2.06/2.28           (k3_xboole_0 @ X0 @ sk_B_1))
% 2.06/2.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 2.06/2.28              (k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1))))),
% 2.06/2.28      inference('sup+', [status(thm)], ['85', '86'])).
% 2.06/2.28  thf('88', plain,
% 2.06/2.28      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.06/2.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.06/2.28  thf('89', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ sk_C_1 @ sk_A)) @ 
% 2.06/2.28           (k3_xboole_0 @ X0 @ sk_B_1))
% 2.06/2.28           = (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_C_1) @ 
% 2.06/2.28              (k3_xboole_0 @ X0 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1))))),
% 2.06/2.28      inference('demod', [status(thm)], ['87', '88'])).
% 2.06/2.28  thf('90', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ 
% 2.06/2.28         (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_C_1 @ sk_A)) @ 
% 2.06/2.28         (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.06/2.28            (k3_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B_1))))),
% 2.06/2.28      inference('sup+', [status(thm)], ['84', '89'])).
% 2.06/2.28  thf('91', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 2.06/2.28      inference('sup-', [status(thm)], ['3', '4'])).
% 2.06/2.28  thf('92', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28         = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['6', '15'])).
% 2.06/2.28  thf('93', plain,
% 2.06/2.28      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.06/2.28  thf('94', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 2.06/2.28      inference('sup+', [status(thm)], ['2', '5'])).
% 2.06/2.28  thf('95', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_C_1 @ sk_D_1)
% 2.06/2.28         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 2.06/2.28  thf('96', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28             (k2_zfmisc_1 @ X0 @ sk_B_1))
% 2.06/2.28          | (r1_tarski @ sk_A @ X0))),
% 2.06/2.28      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 2.06/2.28  thf('97', plain,
% 2.06/2.28      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28           (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['95', '96'])).
% 2.06/2.28  thf('98', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 2.06/2.28      inference('simplify', [status(thm)], ['0'])).
% 2.06/2.28  thf('99', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.06/2.28      inference('demod', [status(thm)], ['97', '98'])).
% 2.06/2.28  thf('100', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.06/2.28      inference('sup+', [status(thm)], ['70', '71'])).
% 2.06/2.28  thf('101', plain,
% 2.06/2.28      (![X13 : $i, X15 : $i]:
% 2.06/2.28         (((X13) = (X15))
% 2.06/2.28          | ~ (r1_tarski @ X15 @ X13)
% 2.06/2.28          | ~ (r1_tarski @ X13 @ X15))),
% 2.06/2.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.06/2.28  thf('102', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.06/2.28          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['100', '101'])).
% 2.06/2.28  thf('103', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.06/2.28      inference('sup-', [status(thm)], ['99', '102'])).
% 2.06/2.28  thf('104', plain,
% 2.06/2.28      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.06/2.28  thf('105', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.06/2.28          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['100', '101'])).
% 2.06/2.28  thf('106', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.06/2.28          | ((X1) = (k3_xboole_0 @ X0 @ X1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['104', '105'])).
% 2.06/2.28  thf('107', plain,
% 2.06/2.28      ((~ (r1_tarski @ sk_C_1 @ sk_A)
% 2.06/2.28        | ((sk_C_1) = (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['103', '106'])).
% 2.06/2.28  thf('108', plain,
% 2.06/2.28      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.06/2.28  thf('109', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.06/2.28      inference('sup-', [status(thm)], ['99', '102'])).
% 2.06/2.28  thf('110', plain, ((~ (r1_tarski @ sk_C_1 @ sk_A) | ((sk_C_1) = (sk_A)))),
% 2.06/2.28      inference('demod', [status(thm)], ['107', '108', '109'])).
% 2.06/2.28  thf('111', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28         = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['6', '15'])).
% 2.06/2.28  thf('112', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.06/2.28      inference('sup-', [status(thm)], ['99', '102'])).
% 2.06/2.28  thf('113', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 2.06/2.28      inference('sup+', [status(thm)], ['24', '29'])).
% 2.06/2.28  thf('114', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1)
% 2.06/2.28           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 2.06/2.28      inference('sup+', [status(thm)], ['7', '8'])).
% 2.06/2.28  thf('115', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.06/2.28  thf('116', plain,
% 2.06/2.28      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.06/2.28      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.06/2.28  thf('117', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.06/2.28      inference('sup+', [status(thm)], ['115', '116'])).
% 2.06/2.28  thf('118', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 2.06/2.28          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['114', '117'])).
% 2.06/2.28  thf('119', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B_1) @ 
% 2.06/2.28          (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['113', '118'])).
% 2.06/2.28  thf('120', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('121', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B_1) @ 
% 2.06/2.28          (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['119', '120'])).
% 2.06/2.28  thf('122', plain,
% 2.06/2.28      (![X20 : $i, X21 : $i]:
% 2.06/2.28         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 2.06/2.28      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.06/2.28  thf('123', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k3_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B_1) @ 
% 2.06/2.28           (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28           = (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B_1))),
% 2.06/2.28      inference('sup-', [status(thm)], ['121', '122'])).
% 2.06/2.28  thf('124', plain,
% 2.06/2.28      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.06/2.28           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.06/2.28              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.06/2.28  thf('125', plain,
% 2.06/2.28      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.06/2.28  thf('126', plain,
% 2.06/2.28      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.06/2.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.06/2.28  thf('127', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_A)) @ 
% 2.06/2.28           (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28           = (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 2.06/2.28  thf('128', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 2.06/2.28         (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 2.06/2.28      inference('sup+', [status(thm)], ['112', '127'])).
% 2.06/2.28  thf('129', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.06/2.28      inference('sup-', [status(thm)], ['99', '102'])).
% 2.06/2.28  thf('130', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.06/2.28      inference('sup-', [status(thm)], ['99', '102'])).
% 2.06/2.28  thf('131', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('132', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))
% 2.06/2.28         = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 2.06/2.28  thf('133', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28             (k2_zfmisc_1 @ sk_A @ X0))
% 2.06/2.28          | (r1_tarski @ sk_B_1 @ X0))),
% 2.06/2.28      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 2.06/2.28  thf('134', plain,
% 2.06/2.28      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28           (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28        | (r1_tarski @ sk_B_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['132', '133'])).
% 2.06/2.28  thf('135', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 2.06/2.28      inference('simplify', [status(thm)], ['0'])).
% 2.06/2.28  thf('136', plain, ((r1_tarski @ sk_B_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['134', '135'])).
% 2.06/2.28  thf('137', plain,
% 2.06/2.28      (![X0 : $i, X1 : $i]:
% 2.06/2.28         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.06/2.28          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['100', '101'])).
% 2.06/2.28  thf('138', plain, (((sk_B_1) = (k3_xboole_0 @ sk_D_1 @ sk_B_1))),
% 2.06/2.28      inference('sup-', [status(thm)], ['136', '137'])).
% 2.06/2.28  thf('139', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_C_1 @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('demod', [status(thm)], ['111', '138'])).
% 2.06/2.28  thf('140', plain,
% 2.06/2.28      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('141', plain,
% 2.06/2.28      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.06/2.28         (((X40) = (k1_xboole_0))
% 2.06/2.28          | (r1_tarski @ X41 @ X42)
% 2.06/2.28          | ~ (r1_tarski @ (k2_zfmisc_1 @ X41 @ X40) @ 
% 2.06/2.28               (k2_zfmisc_1 @ X42 @ X40)))),
% 2.06/2.28      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.06/2.28  thf('142', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 2.06/2.28             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28          | (r1_tarski @ X0 @ sk_A)
% 2.06/2.28          | ((sk_B_1) = (k1_xboole_0)))),
% 2.06/2.28      inference('sup-', [status(thm)], ['140', '141'])).
% 2.06/2.28  thf('143', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('144', plain,
% 2.06/2.28      (![X0 : $i]:
% 2.06/2.28         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B_1) @ 
% 2.06/2.28             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28          | (r1_tarski @ X0 @ sk_A))),
% 2.06/2.28      inference('simplify_reflect-', [status(thm)], ['142', '143'])).
% 2.06/2.28  thf('145', plain,
% 2.06/2.28      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.06/2.28           (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.06/2.28        | (r1_tarski @ sk_C_1 @ sk_A))),
% 2.06/2.28      inference('sup-', [status(thm)], ['139', '144'])).
% 2.06/2.28  thf('146', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 2.06/2.28      inference('simplify', [status(thm)], ['0'])).
% 2.06/2.28  thf('147', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 2.06/2.28      inference('demod', [status(thm)], ['145', '146'])).
% 2.06/2.28  thf('148', plain, (((sk_C_1) = (sk_A))),
% 2.06/2.28      inference('demod', [status(thm)], ['110', '147'])).
% 2.06/2.28  thf('149', plain, ((((sk_C_1) != (sk_C_1)) | ((sk_B_1) = (sk_D_1)))),
% 2.06/2.28      inference('demod', [status(thm)], ['79', '148'])).
% 2.06/2.28  thf('150', plain, (((sk_B_1) = (sk_D_1))),
% 2.06/2.28      inference('simplify', [status(thm)], ['149'])).
% 2.06/2.28  thf('151', plain, ((((sk_A) != (sk_C_1)) | ((sk_B_1) != (sk_D_1)))),
% 2.06/2.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.06/2.28  thf('152', plain, ((((sk_B_1) != (sk_D_1))) <= (~ (((sk_B_1) = (sk_D_1))))),
% 2.06/2.28      inference('split', [status(esa)], ['151'])).
% 2.06/2.28  thf('153', plain, (((sk_C_1) = (sk_A))),
% 2.06/2.28      inference('demod', [status(thm)], ['110', '147'])).
% 2.06/2.28  thf('154', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 2.06/2.28      inference('split', [status(esa)], ['151'])).
% 2.06/2.28  thf('155', plain, ((((sk_C_1) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 2.06/2.28      inference('sup-', [status(thm)], ['153', '154'])).
% 2.06/2.28  thf('156', plain, ((((sk_A) = (sk_C_1)))),
% 2.06/2.28      inference('simplify', [status(thm)], ['155'])).
% 2.06/2.28  thf('157', plain, (~ (((sk_B_1) = (sk_D_1))) | ~ (((sk_A) = (sk_C_1)))),
% 2.06/2.28      inference('split', [status(esa)], ['151'])).
% 2.06/2.28  thf('158', plain, (~ (((sk_B_1) = (sk_D_1)))),
% 2.06/2.28      inference('sat_resolution*', [status(thm)], ['156', '157'])).
% 2.06/2.28  thf('159', plain, (((sk_B_1) != (sk_D_1))),
% 2.06/2.28      inference('simpl_trail', [status(thm)], ['152', '158'])).
% 2.06/2.28  thf('160', plain, ($false),
% 2.06/2.28      inference('simplify_reflect-', [status(thm)], ['150', '159'])).
% 2.06/2.28  
% 2.06/2.28  % SZS output end Refutation
% 2.06/2.28  
% 2.06/2.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
