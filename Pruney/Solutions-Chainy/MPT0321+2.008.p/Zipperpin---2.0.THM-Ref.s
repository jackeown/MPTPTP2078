%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7ZBU5UxXEn

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:34 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 865 expanded)
%              Number of leaves         :   20 ( 273 expanded)
%              Depth                    :   25
%              Number of atoms          :  948 (8896 expanded)
%              Number of equality atoms :  104 (1155 expanded)
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

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

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','3'])).

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
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X22 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X22 @ X23 ) @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k2_xboole_0 @ X18 @ X20 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['24','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_A )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X16 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('41',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ ( k2_xboole_0 @ X18 @ X20 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X21 @ X18 ) @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['24','29'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('48',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['44','45','50'])).

thf('52',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('59',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('61',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('65',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ( ( k2_xboole_0 @ sk_D @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['59','62'])).

thf('69',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ( sk_B = sk_D ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
      = ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('74',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['24','29'])).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('77',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['59','62'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('83',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = sk_D ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_D )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('92',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['69','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','93'])).

thf('95',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['34','94'])).

thf('96',plain,(
    sk_C = sk_A ),
    inference(demod,[status(thm)],['32','95'])).

thf('97',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['69','92'])).

thf('100',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['97'])).

thf('101',plain,
    ( ( sk_D != sk_D )
   <= ( sk_B != sk_D ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_B = sk_D ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['97'])).

thf('104',plain,(
    sk_A != sk_C ),
    inference('sat_resolution*',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_A != sk_C ),
    inference(simpl_trail,[status(thm)],['98','104'])).

thf('106',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['96','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7ZBU5UxXEn
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 839 iterations in 0.380s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.78  thf(commutativity_k2_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.78  thf(t7_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.59/0.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.79  thf(t28_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (![X11 : $i, X12 : $i]:
% 0.59/0.79         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['0', '3'])).
% 0.59/0.79  thf(t134_zfmisc_1, conjecture,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.59/0.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.79         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.59/0.79          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.79            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t120_zfmisc_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.59/0.79         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.59/0.79       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.79         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.79         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 0.59/0.79           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 0.59/0.79              (k2_zfmisc_1 @ X20 @ X19)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.59/0.79           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.59/0.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X11 : $i, X12 : $i]:
% 0.59/0.79         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))
% 0.59/0.79           = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('sup-', [status(thm)], ['9', '10'])).
% 0.59/0.79  thf(t123_zfmisc_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.79     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.59/0.79       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.59/0.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ X22 @ X24) @ (k3_xboole_0 @ X23 @ X25))
% 0.59/0.79           = (k3_xboole_0 @ (k2_zfmisc_1 @ X22 @ X23) @ 
% 0.59/0.79              (k2_zfmisc_1 @ X24 @ X25)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 0.59/0.79           (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['11', '12'])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.59/0.79         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('sup+', [status(thm)], ['4', '13'])).
% 0.59/0.79  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.79  thf(t22_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X9 : $i, X10 : $i]:
% 0.59/0.79         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['15', '16'])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.59/0.79         ((k2_zfmisc_1 @ X21 @ (k2_xboole_0 @ X18 @ X20))
% 0.59/0.79           = (k2_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 0.59/0.79              (k2_zfmisc_1 @ X21 @ X20)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.59/0.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['19', '20'])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         (r1_tarski @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.59/0.79          (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['18', '21'])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         (r1_tarski @ (k2_zfmisc_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.59/0.79          (k2_zfmisc_1 @ X2 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['17', '22'])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      ((r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ (k2_zfmisc_1 @ sk_C @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['14', '23'])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t117_zfmisc_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.59/0.79          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.59/0.79            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.59/0.79          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         (((X15) = (k1_xboole_0))
% 0.59/0.79          | (r1_tarski @ X16 @ X17)
% 0.59/0.79          | ~ (r1_tarski @ (k2_zfmisc_1 @ X16 @ X15) @ 
% 0.59/0.79               (k2_zfmisc_1 @ X17 @ X15)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79             (k2_zfmisc_1 @ X0 @ sk_B))
% 0.59/0.79          | (r1_tarski @ sk_A @ X0)
% 0.59/0.79          | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.79  thf('28', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79             (k2_zfmisc_1 @ X0 @ sk_B))
% 0.59/0.79          | (r1_tarski @ sk_A @ X0))),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.59/0.79  thf('30', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['24', '29'])).
% 0.59/0.79  thf(d10_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      (![X4 : $i, X6 : $i]:
% 0.59/0.79         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('32', plain, ((~ (r1_tarski @ sk_C @ sk_A) | ((sk_C) = (sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('34', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.59/0.79      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.79  thf('35', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         (((X15) = (k1_xboole_0))
% 0.59/0.79          | (r1_tarski @ X16 @ X17)
% 0.59/0.79          | ~ (r1_tarski @ (k2_zfmisc_1 @ X16 @ X15) @ 
% 0.59/0.79               (k2_zfmisc_1 @ X17 @ X15)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.59/0.79  thf('37', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 0.59/0.79             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.59/0.79          | (r1_tarski @ X0 @ sk_A)
% 0.59/0.79          | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.79  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('39', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 0.59/0.79             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.59/0.79          | (r1_tarski @ X0 @ sk_A))),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.59/0.79  thf('40', plain,
% 0.59/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.79         ((k2_zfmisc_1 @ (k2_xboole_0 @ X18 @ X20) @ X19)
% 0.59/0.79           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X19) @ 
% 0.59/0.79              (k2_zfmisc_1 @ X20 @ X19)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.59/0.79  thf('41', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('42', plain,
% 0.59/0.79      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.59/0.79         ((k2_zfmisc_1 @ X21 @ (k2_xboole_0 @ X18 @ X20))
% 0.59/0.79           = (k2_xboole_0 @ (k2_zfmisc_1 @ X21 @ X18) @ 
% 0.59/0.79              (k2_zfmisc_1 @ X21 @ X20)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.59/0.79           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79              (k2_zfmisc_1 @ sk_A @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['41', '42'])).
% 0.59/0.79  thf('44', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_D))
% 0.59/0.79         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 0.59/0.79      inference('sup+', [status(thm)], ['40', '43'])).
% 0.59/0.79  thf('45', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf('46', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['24', '29'])).
% 0.59/0.79  thf(t12_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.59/0.79  thf('47', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]:
% 0.59/0.79         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.79  thf('48', plain, (((k2_xboole_0 @ sk_A @ sk_C) = (sk_C))),
% 0.59/0.79      inference('sup-', [status(thm)], ['46', '47'])).
% 0.59/0.79  thf('49', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.79  thf('50', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['48', '49'])).
% 0.59/0.79  thf('51', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_D @ sk_B))
% 0.59/0.79         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['44', '45', '50'])).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('53', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         (((X15) = (k1_xboole_0))
% 0.59/0.79          | (r1_tarski @ X16 @ X17)
% 0.59/0.79          | ~ (r1_tarski @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 0.59/0.79               (k2_zfmisc_1 @ X15 @ X17)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.59/0.79  thf('54', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 0.59/0.79             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.59/0.79          | (r1_tarski @ X0 @ sk_B)
% 0.59/0.79          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.79  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('56', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 0.59/0.79             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.59/0.79          | (r1_tarski @ X0 @ sk_B))),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.59/0.79  thf('57', plain,
% 0.59/0.79      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79           (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.59/0.79        | (r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['51', '56'])).
% 0.59/0.79  thf('58', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.59/0.79      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.79  thf('59', plain, ((r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_B)),
% 0.59/0.79      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.79  thf('60', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['19', '20'])).
% 0.59/0.79  thf('61', plain,
% 0.59/0.79      (![X4 : $i, X6 : $i]:
% 0.59/0.79         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('62', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.59/0.79          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['60', '61'])).
% 0.59/0.79  thf('63', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['59', '62'])).
% 0.59/0.79  thf('64', plain,
% 0.59/0.79      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.59/0.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.79  thf('65', plain,
% 0.59/0.79      (![X4 : $i, X6 : $i]:
% 0.59/0.79         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('66', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.59/0.79          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.79  thf('67', plain,
% 0.59/0.79      ((~ (r1_tarski @ sk_B @ sk_D) | ((k2_xboole_0 @ sk_D @ sk_B) = (sk_D)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['63', '66'])).
% 0.59/0.79  thf('68', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['59', '62'])).
% 0.59/0.79  thf('69', plain, ((~ (r1_tarski @ sk_B @ sk_D) | ((sk_B) = (sk_D)))),
% 0.59/0.79      inference('demod', [status(thm)], ['67', '68'])).
% 0.59/0.79  thf('70', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.59/0.79      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.79  thf('71', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]:
% 0.59/0.79         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.79  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.79  thf('73', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 0.59/0.79           (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['11', '12'])).
% 0.59/0.79  thf('74', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.59/0.79         (k3_xboole_0 @ sk_D @ sk_B)) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('sup+', [status(thm)], ['72', '73'])).
% 0.59/0.79  thf('75', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.59/0.79      inference('sup-', [status(thm)], ['24', '29'])).
% 0.59/0.79  thf('76', plain,
% 0.59/0.79      (![X11 : $i, X12 : $i]:
% 0.59/0.79         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.79  thf('77', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['75', '76'])).
% 0.59/0.79  thf('78', plain,
% 0.59/0.79      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.79  thf('79', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['77', '78'])).
% 0.59/0.79  thf('80', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_B))
% 0.59/0.79         = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['74', '79'])).
% 0.59/0.79  thf('81', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['59', '62'])).
% 0.59/0.79  thf('82', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.79  thf('83', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (sk_D))),
% 0.59/0.79      inference('sup+', [status(thm)], ['81', '82'])).
% 0.59/0.79  thf('84', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ sk_D) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['80', '83'])).
% 0.59/0.79  thf('85', plain,
% 0.59/0.79      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('86', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.79         (((X15) = (k1_xboole_0))
% 0.59/0.79          | (r1_tarski @ X16 @ X17)
% 0.59/0.79          | ~ (r1_tarski @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 0.59/0.79               (k2_zfmisc_1 @ X15 @ X17)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.59/0.79  thf('87', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79             (k2_zfmisc_1 @ sk_A @ X0))
% 0.59/0.79          | (r1_tarski @ sk_B @ X0)
% 0.59/0.79          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['85', '86'])).
% 0.59/0.79  thf('88', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('89', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79             (k2_zfmisc_1 @ sk_A @ X0))
% 0.59/0.79          | (r1_tarski @ sk_B @ X0))),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.59/0.79  thf('90', plain,
% 0.59/0.79      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 0.59/0.79           (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.59/0.79        | (r1_tarski @ sk_B @ sk_D))),
% 0.59/0.79      inference('sup-', [status(thm)], ['84', '89'])).
% 0.59/0.79  thf('91', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.59/0.79      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.79  thf('92', plain, ((r1_tarski @ sk_B @ sk_D)),
% 0.59/0.79      inference('demod', [status(thm)], ['90', '91'])).
% 0.59/0.79  thf('93', plain, (((sk_B) = (sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['69', '92'])).
% 0.59/0.79  thf('94', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D) @ 
% 0.59/0.79             (k2_zfmisc_1 @ sk_C @ sk_D))
% 0.59/0.79          | (r1_tarski @ X0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['39', '93'])).
% 0.59/0.79  thf('95', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.59/0.79      inference('sup-', [status(thm)], ['34', '94'])).
% 0.59/0.79  thf('96', plain, (((sk_C) = (sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['32', '95'])).
% 0.59/0.79  thf('97', plain, ((((sk_A) != (sk_C)) | ((sk_B) != (sk_D)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('98', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.59/0.79      inference('split', [status(esa)], ['97'])).
% 0.59/0.79  thf('99', plain, (((sk_B) = (sk_D))),
% 0.59/0.79      inference('demod', [status(thm)], ['69', '92'])).
% 0.59/0.79  thf('100', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.59/0.79      inference('split', [status(esa)], ['97'])).
% 0.59/0.79  thf('101', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['99', '100'])).
% 0.59/0.79  thf('102', plain, ((((sk_B) = (sk_D)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['101'])).
% 0.59/0.79  thf('103', plain, (~ (((sk_A) = (sk_C))) | ~ (((sk_B) = (sk_D)))),
% 0.59/0.79      inference('split', [status(esa)], ['97'])).
% 0.59/0.79  thf('104', plain, (~ (((sk_A) = (sk_C)))),
% 0.59/0.79      inference('sat_resolution*', [status(thm)], ['102', '103'])).
% 0.59/0.79  thf('105', plain, (((sk_A) != (sk_C))),
% 0.59/0.79      inference('simpl_trail', [status(thm)], ['98', '104'])).
% 0.59/0.79  thf('106', plain, ($false),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['96', '105'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
