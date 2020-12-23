%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Mno8cWkbd

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:33 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  169 (1626 expanded)
%              Number of leaves         :   24 ( 534 expanded)
%              Depth                    :   27
%              Number of atoms          : 1377 (16599 expanded)
%              Number of equality atoms :  144 (2073 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_C_1 ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X43 @ X45 ) @ X44 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X43: $i,X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ X46 @ ( k2_xboole_0 @ X43 @ X45 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X46 @ X43 ) @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('9',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ ( k2_xboole_0 @ sk_D_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ X1 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_D_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_D_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k4_xboole_0 @ X30 @ X31 ) )
      = ( k3_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k4_xboole_0 @ X30 @ X31 ) )
      = ( k3_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','24','25','26','33'])).

thf('35',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('36',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r1_tarski @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X41 @ X40 ) @ ( k2_zfmisc_1 @ X42 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','47','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X22 @ X23 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X1
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_A )
    | ( sk_C_1
      = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_A )
    | ( sk_C_1 = sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('65',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r1_tarski @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X41 @ X40 ) @ ( k2_zfmisc_1 @ X42 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X43 @ X45 ) @ X44 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('71',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X43: $i,X45: $i,X46: $i] :
      ( ( k2_zfmisc_1 @ X46 @ ( k2_xboole_0 @ X43 @ X45 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X46 @ X43 ) @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_D_1 ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('76',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_D_1 @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r1_tarski @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X40 @ X41 ) @ ( k2_zfmisc_1 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_D_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('84',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('87',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_D_1 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['82','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('89',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_xboole_0 @ sk_D_1 @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('95',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
    | ( ( k2_xboole_0 @ sk_D_1 @ sk_B )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k2_xboole_0 @ sk_D_1 @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['87','92'])).

thf('99',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_1 )
    | ( sk_B = sk_D_1 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('101',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('105',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k4_xboole_0 @ X30 @ X31 ) )
      = ( k3_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('113',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X47 @ X49 ) @ ( k3_xboole_0 @ X48 @ X50 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X47 @ X48 ) @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( k2_xboole_0 @ sk_D_1 @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['87','92'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('117',plain,
    ( sk_D_1
    = ( k3_xboole_0 @ sk_D_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['114','117'])).

thf('119',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['102','118'])).

thf('120',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('121',plain,
    ( ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 )
    = ( k2_zfmisc_1 @ sk_A @ sk_D_1 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r1_tarski @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X40 @ X41 ) @ ( k2_zfmisc_1 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
    | ( r1_tarski @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['121','126'])).

thf('128',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('129',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    sk_B = sk_D_1 ),
    inference(demod,[status(thm)],['99','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','130'])).

thf('132',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['64','131'])).

thf('133',plain,(
    sk_C_1 = sk_A ),
    inference(demod,[status(thm)],['63','132'])).

thf('134',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['134'])).

thf('136',plain,(
    sk_B = sk_D_1 ),
    inference(demod,[status(thm)],['99','129'])).

thf('137',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['134'])).

thf('138',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    sk_B = sk_D_1 ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['134'])).

thf('141',plain,(
    sk_A != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['139','140'])).

thf('142',plain,(
    sk_A != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['135','141'])).

thf('143',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['133','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Mno8cWkbd
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.21/2.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.21/2.45  % Solved by: fo/fo7.sh
% 2.21/2.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.21/2.45  % done 2988 iterations in 1.946s
% 2.21/2.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.21/2.45  % SZS output start Refutation
% 2.21/2.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.21/2.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.21/2.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.21/2.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.21/2.45  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.21/2.45  thf(sk_B_type, type, sk_B: $i).
% 2.21/2.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.21/2.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.21/2.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.21/2.45  thf(sk_A_type, type, sk_A: $i).
% 2.21/2.45  thf(t134_zfmisc_1, conjecture,
% 2.21/2.45    (![A:$i,B:$i,C:$i,D:$i]:
% 2.21/2.45     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.21/2.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.21/2.45         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 2.21/2.45  thf(zf_stmt_0, negated_conjecture,
% 2.21/2.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.21/2.45        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.21/2.45          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.21/2.45            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 2.21/2.45    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 2.21/2.45  thf('0', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf(t123_zfmisc_1, axiom,
% 2.21/2.45    (![A:$i,B:$i,C:$i,D:$i]:
% 2.21/2.45     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 2.21/2.45       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 2.21/2.45  thf('1', plain,
% 2.21/2.45      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.21/2.45           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.21/2.45  thf('2', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 2.21/2.45           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 2.21/2.45              (k2_zfmisc_1 @ sk_C_1 @ sk_D_1)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['0', '1'])).
% 2.21/2.45  thf('3', plain,
% 2.21/2.45      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.21/2.45           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.21/2.45  thf('4', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 2.21/2.45           = (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_C_1) @ 
% 2.21/2.45              (k3_xboole_0 @ X0 @ sk_D_1)))),
% 2.21/2.45      inference('demod', [status(thm)], ['2', '3'])).
% 2.21/2.45  thf('5', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf(t120_zfmisc_1, axiom,
% 2.21/2.45    (![A:$i,B:$i,C:$i]:
% 2.21/2.45     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 2.21/2.45         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 2.21/2.45       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.21/2.45         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 2.21/2.45  thf('6', plain,
% 2.21/2.45      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k2_xboole_0 @ X43 @ X45) @ X44)
% 2.21/2.45           = (k2_xboole_0 @ (k2_zfmisc_1 @ X43 @ X44) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X45 @ X44)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 2.21/2.45  thf('7', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 2.21/2.45           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['5', '6'])).
% 2.21/2.45  thf('8', plain,
% 2.21/2.45      (![X43 : $i, X45 : $i, X46 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ X46 @ (k2_xboole_0 @ X43 @ X45))
% 2.21/2.45           = (k2_xboole_0 @ (k2_zfmisc_1 @ X46 @ X43) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X46 @ X45)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 2.21/2.45  thf('9', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B))
% 2.21/2.45         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 2.21/2.45      inference('sup+', [status(thm)], ['7', '8'])).
% 2.21/2.45  thf(commutativity_k2_xboole_0, axiom,
% 2.21/2.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.21/2.45  thf('10', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.21/2.45  thf('11', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B))
% 2.21/2.45         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B))),
% 2.21/2.45      inference('demod', [status(thm)], ['9', '10'])).
% 2.21/2.45  thf('12', plain,
% 2.21/2.45      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.21/2.45           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.21/2.45  thf('13', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ X1) @ 
% 2.21/2.45           (k3_xboole_0 @ sk_B @ X0))
% 2.21/2.45           = (k3_xboole_0 @ 
% 2.21/2.45              (k2_zfmisc_1 @ sk_C_1 @ (k2_xboole_0 @ sk_D_1 @ sk_B)) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X1 @ X0)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['11', '12'])).
% 2.21/2.45  thf('14', plain,
% 2.21/2.45      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.21/2.45           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.21/2.45  thf('15', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ X1) @ 
% 2.21/2.45           (k3_xboole_0 @ sk_B @ X0))
% 2.21/2.45           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ X1) @ 
% 2.21/2.45              (k3_xboole_0 @ (k2_xboole_0 @ sk_D_1 @ sk_B) @ X0)))),
% 2.21/2.45      inference('demod', [status(thm)], ['13', '14'])).
% 2.21/2.45  thf('16', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ 
% 2.21/2.45         (k3_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_C_1) @ 
% 2.21/2.45         (k3_xboole_0 @ sk_B @ sk_D_1))
% 2.21/2.45         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 2.21/2.45            (k3_xboole_0 @ (k2_xboole_0 @ sk_D_1 @ sk_B) @ sk_B)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['4', '15'])).
% 2.21/2.45  thf(commutativity_k3_xboole_0, axiom,
% 2.21/2.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.21/2.45  thf('17', plain,
% 2.21/2.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.45  thf(t7_xboole_1, axiom,
% 2.21/2.45    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.21/2.45  thf('18', plain,
% 2.21/2.45      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 2.21/2.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.21/2.45  thf(l32_xboole_1, axiom,
% 2.21/2.45    (![A:$i,B:$i]:
% 2.21/2.45     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.21/2.45  thf('19', plain,
% 2.21/2.45      (![X17 : $i, X19 : $i]:
% 2.21/2.45         (((k4_xboole_0 @ X17 @ X19) = (k1_xboole_0))
% 2.21/2.45          | ~ (r1_tarski @ X17 @ X19))),
% 2.21/2.45      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.21/2.45  thf('20', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.21/2.45      inference('sup-', [status(thm)], ['18', '19'])).
% 2.21/2.45  thf(t48_xboole_1, axiom,
% 2.21/2.45    (![A:$i,B:$i]:
% 2.21/2.45     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.21/2.45  thf('21', plain,
% 2.21/2.45      (![X30 : $i, X31 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ X30 @ (k4_xboole_0 @ X30 @ X31))
% 2.21/2.45           = (k3_xboole_0 @ X30 @ X31))),
% 2.21/2.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.21/2.45  thf('22', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 2.21/2.45           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['20', '21'])).
% 2.21/2.45  thf(t3_boole, axiom,
% 2.21/2.45    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.21/2.45  thf('23', plain, (![X27 : $i]: ((k4_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 2.21/2.45      inference('cnf', [status(esa)], [t3_boole])).
% 2.21/2.45  thf('24', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.21/2.45      inference('demod', [status(thm)], ['22', '23'])).
% 2.21/2.45  thf('25', plain,
% 2.21/2.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.45  thf('26', plain,
% 2.21/2.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.45  thf('27', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.21/2.45  thf('28', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.21/2.45      inference('sup-', [status(thm)], ['18', '19'])).
% 2.21/2.45  thf('29', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.21/2.45      inference('sup+', [status(thm)], ['27', '28'])).
% 2.21/2.45  thf('30', plain,
% 2.21/2.45      (![X30 : $i, X31 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ X30 @ (k4_xboole_0 @ X30 @ X31))
% 2.21/2.45           = (k3_xboole_0 @ X30 @ X31))),
% 2.21/2.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.21/2.45  thf('31', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 2.21/2.45           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['29', '30'])).
% 2.21/2.45  thf('32', plain, (![X27 : $i]: ((k4_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 2.21/2.45      inference('cnf', [status(esa)], [t3_boole])).
% 2.21/2.45  thf('33', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.21/2.45      inference('demod', [status(thm)], ['31', '32'])).
% 2.21/2.45  thf('34', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B))
% 2.21/2.45         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_B))),
% 2.21/2.45      inference('demod', [status(thm)], ['16', '17', '24', '25', '26', '33'])).
% 2.21/2.45  thf('35', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf(t117_zfmisc_1, axiom,
% 2.21/2.45    (![A:$i,B:$i,C:$i]:
% 2.21/2.45     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.21/2.45          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 2.21/2.45            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 2.21/2.45          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 2.21/2.45  thf('36', plain,
% 2.21/2.45      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.21/2.45         (((X40) = (k1_xboole_0))
% 2.21/2.45          | (r1_tarski @ X41 @ X42)
% 2.21/2.45          | ~ (r1_tarski @ (k2_zfmisc_1 @ X41 @ X40) @ 
% 2.21/2.45               (k2_zfmisc_1 @ X42 @ X40)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.21/2.45  thf('37', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45             (k2_zfmisc_1 @ X0 @ sk_B))
% 2.21/2.45          | (r1_tarski @ sk_A @ X0)
% 2.21/2.45          | ((sk_B) = (k1_xboole_0)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['35', '36'])).
% 2.21/2.45  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf('39', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45             (k2_zfmisc_1 @ X0 @ sk_B))
% 2.21/2.45          | (r1_tarski @ sk_A @ X0))),
% 2.21/2.45      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 2.21/2.45  thf('40', plain,
% 2.21/2.45      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45           (k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))
% 2.21/2.45        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['34', '39'])).
% 2.21/2.45  thf('41', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.21/2.45      inference('demod', [status(thm)], ['31', '32'])).
% 2.21/2.45  thf('42', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 2.21/2.45           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['5', '6'])).
% 2.21/2.45  thf('43', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.21/2.45      inference('demod', [status(thm)], ['22', '23'])).
% 2.21/2.45  thf('44', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ sk_C_1 @ sk_D_1)
% 2.21/2.45           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45              (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['42', '43'])).
% 2.21/2.45  thf('45', plain,
% 2.21/2.45      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.21/2.45           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.21/2.45  thf('46', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ sk_C_1 @ sk_D_1)
% 2.21/2.45           = (k2_zfmisc_1 @ 
% 2.21/2.45              (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 2.21/2.45              (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 2.21/2.45      inference('demod', [status(thm)], ['44', '45'])).
% 2.21/2.45  thf('47', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_C_1 @ sk_D_1)
% 2.21/2.45         = (k2_zfmisc_1 @ sk_C_1 @ (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['41', '46'])).
% 2.21/2.45  thf(d10_xboole_0, axiom,
% 2.21/2.45    (![A:$i,B:$i]:
% 2.21/2.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.21/2.45  thf('48', plain,
% 2.21/2.45      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 2.21/2.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.21/2.45  thf('49', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 2.21/2.45      inference('simplify', [status(thm)], ['48'])).
% 2.21/2.45  thf('50', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.21/2.45      inference('demod', [status(thm)], ['40', '47', '49'])).
% 2.21/2.45  thf('51', plain,
% 2.21/2.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.45  thf(t17_xboole_1, axiom,
% 2.21/2.45    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.21/2.45  thf('52', plain,
% 2.21/2.45      (![X22 : $i, X23 : $i]: (r1_tarski @ (k3_xboole_0 @ X22 @ X23) @ X22)),
% 2.21/2.45      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.21/2.45  thf('53', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.21/2.45      inference('sup+', [status(thm)], ['51', '52'])).
% 2.21/2.45  thf('54', plain,
% 2.21/2.45      (![X14 : $i, X16 : $i]:
% 2.21/2.45         (((X14) = (X16))
% 2.21/2.45          | ~ (r1_tarski @ X16 @ X14)
% 2.21/2.45          | ~ (r1_tarski @ X14 @ X16))),
% 2.21/2.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.21/2.45  thf('55', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.21/2.45          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['53', '54'])).
% 2.21/2.45  thf('56', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.21/2.45      inference('sup-', [status(thm)], ['50', '55'])).
% 2.21/2.45  thf('57', plain,
% 2.21/2.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.45  thf('58', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.21/2.45          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['53', '54'])).
% 2.21/2.45  thf('59', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.21/2.45          | ((X1) = (k3_xboole_0 @ X0 @ X1)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['57', '58'])).
% 2.21/2.45  thf('60', plain,
% 2.21/2.45      ((~ (r1_tarski @ sk_C_1 @ sk_A)
% 2.21/2.45        | ((sk_C_1) = (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['56', '59'])).
% 2.21/2.45  thf('61', plain,
% 2.21/2.45      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.21/2.45  thf('62', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.21/2.45      inference('sup-', [status(thm)], ['50', '55'])).
% 2.21/2.45  thf('63', plain, ((~ (r1_tarski @ sk_C_1 @ sk_A) | ((sk_C_1) = (sk_A)))),
% 2.21/2.45      inference('demod', [status(thm)], ['60', '61', '62'])).
% 2.21/2.45  thf('64', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 2.21/2.45      inference('simplify', [status(thm)], ['48'])).
% 2.21/2.45  thf('65', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf('66', plain,
% 2.21/2.45      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.21/2.45         (((X40) = (k1_xboole_0))
% 2.21/2.45          | (r1_tarski @ X41 @ X42)
% 2.21/2.45          | ~ (r1_tarski @ (k2_zfmisc_1 @ X41 @ X40) @ 
% 2.21/2.45               (k2_zfmisc_1 @ X42 @ X40)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.21/2.45  thf('67', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 2.21/2.45             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.21/2.45          | (r1_tarski @ X0 @ sk_A)
% 2.21/2.45          | ((sk_B) = (k1_xboole_0)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['65', '66'])).
% 2.21/2.45  thf('68', plain, (((sk_B) != (k1_xboole_0))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf('69', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 2.21/2.45             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.21/2.45          | (r1_tarski @ X0 @ sk_A))),
% 2.21/2.45      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 2.21/2.45  thf('70', plain,
% 2.21/2.45      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k2_xboole_0 @ X43 @ X45) @ X44)
% 2.21/2.45           = (k2_xboole_0 @ (k2_zfmisc_1 @ X43 @ X44) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X45 @ X44)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 2.21/2.45  thf('71', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf('72', plain,
% 2.21/2.45      (![X43 : $i, X45 : $i, X46 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ X46 @ (k2_xboole_0 @ X43 @ X45))
% 2.21/2.45           = (k2_xboole_0 @ (k2_zfmisc_1 @ X46 @ X43) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X46 @ X45)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 2.21/2.45  thf('73', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 2.21/2.45           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45              (k2_zfmisc_1 @ sk_A @ X0)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['71', '72'])).
% 2.21/2.45  thf('74', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_D_1))
% 2.21/2.45         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_D_1))),
% 2.21/2.45      inference('sup+', [status(thm)], ['70', '73'])).
% 2.21/2.45  thf('75', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.21/2.45  thf('76', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_D_1 @ sk_B))
% 2.21/2.45         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_D_1))),
% 2.21/2.45      inference('demod', [status(thm)], ['74', '75'])).
% 2.21/2.45  thf('77', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf('78', plain,
% 2.21/2.45      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.21/2.45         (((X40) = (k1_xboole_0))
% 2.21/2.45          | (r1_tarski @ X41 @ X42)
% 2.21/2.45          | ~ (r1_tarski @ (k2_zfmisc_1 @ X40 @ X41) @ 
% 2.21/2.45               (k2_zfmisc_1 @ X40 @ X42)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.21/2.45  thf('79', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 2.21/2.45             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.21/2.45          | (r1_tarski @ X0 @ sk_B)
% 2.21/2.45          | ((sk_A) = (k1_xboole_0)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['77', '78'])).
% 2.21/2.45  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf('81', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 2.21/2.45             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.21/2.45          | (r1_tarski @ X0 @ sk_B))),
% 2.21/2.45      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 2.21/2.45  thf('82', plain,
% 2.21/2.45      ((~ (r1_tarski @ 
% 2.21/2.45           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_D_1) @ 
% 2.21/2.45           (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.21/2.45        | (r1_tarski @ (k2_xboole_0 @ sk_D_1 @ sk_B) @ sk_B))),
% 2.21/2.45      inference('sup-', [status(thm)], ['76', '81'])).
% 2.21/2.45  thf('83', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.21/2.45      inference('sup-', [status(thm)], ['50', '55'])).
% 2.21/2.45  thf(t22_xboole_1, axiom,
% 2.21/2.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 2.21/2.45  thf('84', plain,
% 2.21/2.45      (![X24 : $i, X25 : $i]:
% 2.21/2.45         ((k2_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)) = (X24))),
% 2.21/2.45      inference('cnf', [status(esa)], [t22_xboole_1])).
% 2.21/2.45  thf('85', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 2.21/2.45      inference('sup+', [status(thm)], ['83', '84'])).
% 2.21/2.45  thf('86', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 2.21/2.45      inference('simplify', [status(thm)], ['48'])).
% 2.21/2.45  thf('87', plain, ((r1_tarski @ (k2_xboole_0 @ sk_D_1 @ sk_B) @ sk_B)),
% 2.21/2.45      inference('demod', [status(thm)], ['82', '85', '86'])).
% 2.21/2.45  thf('88', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.21/2.45  thf('89', plain,
% 2.21/2.45      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 2.21/2.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.21/2.45  thf('90', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.21/2.45      inference('sup+', [status(thm)], ['88', '89'])).
% 2.21/2.45  thf('91', plain,
% 2.21/2.45      (![X14 : $i, X16 : $i]:
% 2.21/2.45         (((X14) = (X16))
% 2.21/2.45          | ~ (r1_tarski @ X16 @ X14)
% 2.21/2.45          | ~ (r1_tarski @ X14 @ X16))),
% 2.21/2.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.21/2.45  thf('92', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 2.21/2.45          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['90', '91'])).
% 2.21/2.45  thf('93', plain, (((k2_xboole_0 @ sk_D_1 @ sk_B) = (sk_B))),
% 2.21/2.45      inference('sup-', [status(thm)], ['87', '92'])).
% 2.21/2.45  thf('94', plain,
% 2.21/2.45      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 2.21/2.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.21/2.45  thf('95', plain,
% 2.21/2.45      (![X14 : $i, X16 : $i]:
% 2.21/2.45         (((X14) = (X16))
% 2.21/2.45          | ~ (r1_tarski @ X16 @ X14)
% 2.21/2.45          | ~ (r1_tarski @ X14 @ X16))),
% 2.21/2.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.21/2.45  thf('96', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.21/2.45          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['94', '95'])).
% 2.21/2.45  thf('97', plain,
% 2.21/2.45      ((~ (r1_tarski @ sk_B @ sk_D_1)
% 2.21/2.45        | ((k2_xboole_0 @ sk_D_1 @ sk_B) = (sk_D_1)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['93', '96'])).
% 2.21/2.45  thf('98', plain, (((k2_xboole_0 @ sk_D_1 @ sk_B) = (sk_B))),
% 2.21/2.45      inference('sup-', [status(thm)], ['87', '92'])).
% 2.21/2.45  thf('99', plain, ((~ (r1_tarski @ sk_B @ sk_D_1) | ((sk_B) = (sk_D_1)))),
% 2.21/2.45      inference('demod', [status(thm)], ['97', '98'])).
% 2.21/2.45  thf('100', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 2.21/2.45      inference('simplify', [status(thm)], ['48'])).
% 2.21/2.45  thf(t12_xboole_1, axiom,
% 2.21/2.45    (![A:$i,B:$i]:
% 2.21/2.45     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.21/2.45  thf('101', plain,
% 2.21/2.45      (![X20 : $i, X21 : $i]:
% 2.21/2.45         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 2.21/2.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.21/2.45  thf('102', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.21/2.45      inference('sup-', [status(thm)], ['100', '101'])).
% 2.21/2.45  thf('103', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.21/2.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.21/2.45  thf('104', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 2.21/2.45           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['5', '6'])).
% 2.21/2.45  thf('105', plain,
% 2.21/2.45      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 2.21/2.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.21/2.45  thf('106', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 2.21/2.45      inference('sup+', [status(thm)], ['104', '105'])).
% 2.21/2.45  thf('107', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45          (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 2.21/2.45      inference('sup+', [status(thm)], ['103', '106'])).
% 2.21/2.45  thf('108', plain,
% 2.21/2.45      (![X17 : $i, X19 : $i]:
% 2.21/2.45         (((k4_xboole_0 @ X17 @ X19) = (k1_xboole_0))
% 2.21/2.45          | ~ (r1_tarski @ X17 @ X19))),
% 2.21/2.45      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.21/2.45  thf('109', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45           (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B)) = (k1_xboole_0))),
% 2.21/2.45      inference('sup-', [status(thm)], ['107', '108'])).
% 2.21/2.45  thf('110', plain,
% 2.21/2.45      (![X30 : $i, X31 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ X30 @ (k4_xboole_0 @ X30 @ X31))
% 2.21/2.45           = (k3_xboole_0 @ X30 @ X31))),
% 2.21/2.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.21/2.45  thf('111', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ k1_xboole_0)
% 2.21/2.45           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45              (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B)))),
% 2.21/2.45      inference('sup+', [status(thm)], ['109', '110'])).
% 2.21/2.45  thf('112', plain, (![X27 : $i]: ((k4_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 2.21/2.45      inference('cnf', [status(esa)], [t3_boole])).
% 2.21/2.45  thf('113', plain,
% 2.21/2.45      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ (k3_xboole_0 @ X47 @ X49) @ (k3_xboole_0 @ X48 @ X50))
% 2.21/2.45           = (k3_xboole_0 @ (k2_zfmisc_1 @ X47 @ X48) @ 
% 2.21/2.45              (k2_zfmisc_1 @ X49 @ X50)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 2.21/2.45  thf('114', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ sk_C_1 @ sk_D_1)
% 2.21/2.45           = (k2_zfmisc_1 @ 
% 2.21/2.45              (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_A)) @ 
% 2.21/2.45              (k3_xboole_0 @ sk_D_1 @ sk_B)))),
% 2.21/2.45      inference('demod', [status(thm)], ['111', '112', '113'])).
% 2.21/2.45  thf('115', plain, (((k2_xboole_0 @ sk_D_1 @ sk_B) = (sk_B))),
% 2.21/2.45      inference('sup-', [status(thm)], ['87', '92'])).
% 2.21/2.45  thf('116', plain,
% 2.21/2.45      (![X0 : $i, X1 : $i]:
% 2.21/2.45         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.21/2.45      inference('demod', [status(thm)], ['22', '23'])).
% 2.21/2.45  thf('117', plain, (((sk_D_1) = (k3_xboole_0 @ sk_D_1 @ sk_B))),
% 2.21/2.45      inference('sup+', [status(thm)], ['115', '116'])).
% 2.21/2.45  thf('118', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         ((k2_zfmisc_1 @ sk_C_1 @ sk_D_1)
% 2.21/2.45           = (k2_zfmisc_1 @ 
% 2.21/2.45              (k3_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_A)) @ sk_D_1))),
% 2.21/2.45      inference('demod', [status(thm)], ['114', '117'])).
% 2.21/2.45  thf('119', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_C_1 @ sk_D_1)
% 2.21/2.45         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_D_1))),
% 2.21/2.45      inference('sup+', [status(thm)], ['102', '118'])).
% 2.21/2.45  thf('120', plain, (((sk_A) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 2.21/2.45      inference('sup-', [status(thm)], ['50', '55'])).
% 2.21/2.45  thf('121', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_C_1 @ sk_D_1) = (k2_zfmisc_1 @ sk_A @ sk_D_1))),
% 2.21/2.45      inference('demod', [status(thm)], ['119', '120'])).
% 2.21/2.45  thf('122', plain,
% 2.21/2.45      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf('123', plain,
% 2.21/2.45      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.21/2.45         (((X40) = (k1_xboole_0))
% 2.21/2.45          | (r1_tarski @ X41 @ X42)
% 2.21/2.45          | ~ (r1_tarski @ (k2_zfmisc_1 @ X40 @ X41) @ 
% 2.21/2.45               (k2_zfmisc_1 @ X40 @ X42)))),
% 2.21/2.45      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 2.21/2.45  thf('124', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45             (k2_zfmisc_1 @ sk_A @ X0))
% 2.21/2.45          | (r1_tarski @ sk_B @ X0)
% 2.21/2.45          | ((sk_A) = (k1_xboole_0)))),
% 2.21/2.45      inference('sup-', [status(thm)], ['122', '123'])).
% 2.21/2.45  thf('125', plain, (((sk_A) != (k1_xboole_0))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf('126', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45             (k2_zfmisc_1 @ sk_A @ X0))
% 2.21/2.45          | (r1_tarski @ sk_B @ X0))),
% 2.21/2.45      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 2.21/2.45  thf('127', plain,
% 2.21/2.45      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C_1 @ sk_D_1) @ 
% 2.21/2.45           (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.21/2.45        | (r1_tarski @ sk_B @ sk_D_1))),
% 2.21/2.45      inference('sup-', [status(thm)], ['121', '126'])).
% 2.21/2.45  thf('128', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 2.21/2.45      inference('simplify', [status(thm)], ['48'])).
% 2.21/2.45  thf('129', plain, ((r1_tarski @ sk_B @ sk_D_1)),
% 2.21/2.45      inference('demod', [status(thm)], ['127', '128'])).
% 2.21/2.45  thf('130', plain, (((sk_B) = (sk_D_1))),
% 2.21/2.45      inference('demod', [status(thm)], ['99', '129'])).
% 2.21/2.45  thf('131', plain,
% 2.21/2.45      (![X0 : $i]:
% 2.21/2.45         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D_1) @ 
% 2.21/2.45             (k2_zfmisc_1 @ sk_C_1 @ sk_D_1))
% 2.21/2.45          | (r1_tarski @ X0 @ sk_A))),
% 2.21/2.45      inference('demod', [status(thm)], ['69', '130'])).
% 2.21/2.45  thf('132', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 2.21/2.45      inference('sup-', [status(thm)], ['64', '131'])).
% 2.21/2.45  thf('133', plain, (((sk_C_1) = (sk_A))),
% 2.21/2.45      inference('demod', [status(thm)], ['63', '132'])).
% 2.21/2.45  thf('134', plain, ((((sk_A) != (sk_C_1)) | ((sk_B) != (sk_D_1)))),
% 2.21/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.21/2.45  thf('135', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 2.21/2.45      inference('split', [status(esa)], ['134'])).
% 2.21/2.45  thf('136', plain, (((sk_B) = (sk_D_1))),
% 2.21/2.45      inference('demod', [status(thm)], ['99', '129'])).
% 2.21/2.45  thf('137', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 2.21/2.45      inference('split', [status(esa)], ['134'])).
% 2.21/2.45  thf('138', plain, ((((sk_D_1) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 2.21/2.45      inference('sup-', [status(thm)], ['136', '137'])).
% 2.21/2.45  thf('139', plain, ((((sk_B) = (sk_D_1)))),
% 2.21/2.45      inference('simplify', [status(thm)], ['138'])).
% 2.21/2.45  thf('140', plain, (~ (((sk_A) = (sk_C_1))) | ~ (((sk_B) = (sk_D_1)))),
% 2.21/2.45      inference('split', [status(esa)], ['134'])).
% 2.21/2.45  thf('141', plain, (~ (((sk_A) = (sk_C_1)))),
% 2.21/2.45      inference('sat_resolution*', [status(thm)], ['139', '140'])).
% 2.21/2.45  thf('142', plain, (((sk_A) != (sk_C_1))),
% 2.21/2.45      inference('simpl_trail', [status(thm)], ['135', '141'])).
% 2.21/2.45  thf('143', plain, ($false),
% 2.21/2.45      inference('simplify_reflect-', [status(thm)], ['133', '142'])).
% 2.21/2.45  
% 2.21/2.45  % SZS output end Refutation
% 2.21/2.45  
% 2.21/2.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
