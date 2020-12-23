%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cPlbF0pFrY

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:43 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 330 expanded)
%              Number of leaves         :   32 ( 111 expanded)
%              Depth                    :   22
%              Number of atoms          : 1084 (2810 expanded)
%              Number of equality atoms :   95 ( 244 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ X42 @ X43 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X42 @ X44 ) @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X45 @ X47 ) @ ( k3_xboole_0 @ X46 @ X48 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X45 @ X46 ) @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('16',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('17',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r1_tarski @ X40 @ X41 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X39 @ X40 ) @ ( k2_zfmisc_1 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) )
      | ( ( k3_xboole_0 @ sk_A @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('21',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_D_2 ) @ sk_B )
    | ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ sk_D_2 )
    | ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_2 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('37',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('38',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X45 @ X47 ) @ ( k3_xboole_0 @ X46 @ X48 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X45 @ X46 ) @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) )
      | ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','52'])).

thf('54',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','53'])).

thf('55',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r1_tarski @ X40 @ X41 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X40 @ X39 ) @ ( k2_zfmisc_1 @ X41 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('56',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('58',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['35','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_2 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['33'])).

thf('61',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D_2 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X32: $i,X33: $i,X36: $i] :
      ( ( X36
        = ( k2_zfmisc_1 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X36 @ X32 @ X33 ) @ ( sk_E @ X36 @ X32 @ X33 ) @ ( sk_D_1 @ X36 @ X32 @ X33 ) @ X32 @ X33 )
      | ( r2_hidden @ ( sk_D_1 @ X36 @ X32 @ X33 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('69',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ X26 )
      | ~ ( zip_tseitin_0 @ X24 @ X23 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('72',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('73',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['74'])).

thf('78',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('81',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['33'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['78','90'])).

thf('92',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D_2 )
    | ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['33'])).

thf('94',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['67','94'])).

thf('96',plain,(
    ! [X32: $i,X33: $i,X36: $i] :
      ( ( X36
        = ( k2_zfmisc_1 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X36 @ X32 @ X33 ) @ ( sk_E @ X36 @ X32 @ X33 ) @ ( sk_D_1 @ X36 @ X32 @ X33 ) @ X32 @ X33 )
      | ( r2_hidden @ ( sk_D_1 @ X36 @ X32 @ X33 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X23 @ X27 )
      | ~ ( zip_tseitin_0 @ X24 @ X23 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['74'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['74'])).

thf('102',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['95','102'])).

thf('104',plain,(
    $false ),
    inference(simplify,[status(thm)],['103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cPlbF0pFrY
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.01/1.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.21  % Solved by: fo/fo7.sh
% 1.01/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.21  % done 1784 iterations in 0.757s
% 1.01/1.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.21  % SZS output start Refutation
% 1.01/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.21  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 1.01/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.21  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 1.01/1.21  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.01/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 1.01/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.01/1.21  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.01/1.21  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.01/1.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.01/1.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.01/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.21  thf(sk_C_type, type, sk_C: $i).
% 1.01/1.21  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.01/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.01/1.21  thf(t48_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.01/1.21  thf('0', plain,
% 1.01/1.21      (![X21 : $i, X22 : $i]:
% 1.01/1.21         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.01/1.21           = (k3_xboole_0 @ X21 @ X22))),
% 1.01/1.21      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.21  thf(d10_xboole_0, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.01/1.21  thf('1', plain,
% 1.01/1.21      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.01/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.01/1.21  thf('2', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.01/1.21      inference('simplify', [status(thm)], ['1'])).
% 1.01/1.21  thf(t106_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.01/1.21       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.01/1.21  thf('3', plain,
% 1.01/1.21      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.01/1.21         ((r1_tarski @ X12 @ X13)
% 1.01/1.21          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.01/1.22  thf('4', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 1.01/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.22  thf('5', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.01/1.22      inference('sup+', [status(thm)], ['0', '4'])).
% 1.01/1.22  thf(t118_zfmisc_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ( r1_tarski @ A @ B ) =>
% 1.01/1.22       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 1.01/1.22         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 1.01/1.22  thf('6', plain,
% 1.01/1.22      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X42 @ X43)
% 1.01/1.22          | (r1_tarski @ (k2_zfmisc_1 @ X42 @ X44) @ (k2_zfmisc_1 @ X43 @ X44)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 1.01/1.22  thf('7', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.22         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 1.01/1.22          (k2_zfmisc_1 @ X0 @ X2))),
% 1.01/1.22      inference('sup-', [status(thm)], ['5', '6'])).
% 1.01/1.22  thf(t138_zfmisc_1, conjecture,
% 1.01/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.22     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.01/1.22       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 1.01/1.22         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 1.01/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.22    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.22        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.01/1.22          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 1.01/1.22            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 1.01/1.22    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 1.01/1.22  thf('8', plain,
% 1.01/1.22      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D_2))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf(l32_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.01/1.22  thf('9', plain,
% 1.01/1.22      (![X9 : $i, X11 : $i]:
% 1.01/1.22         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.01/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.01/1.22  thf('10', plain,
% 1.01/1.22      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.01/1.22         (k2_zfmisc_1 @ sk_C @ sk_D_2)) = (k1_xboole_0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['8', '9'])).
% 1.01/1.22  thf('11', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.01/1.22           = (k3_xboole_0 @ X21 @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.22  thf('12', plain,
% 1.01/1.22      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.01/1.22         = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.01/1.22            (k2_zfmisc_1 @ sk_C @ sk_D_2)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['10', '11'])).
% 1.01/1.22  thf(t3_boole, axiom,
% 1.01/1.22    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.01/1.22  thf('13', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 1.01/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.01/1.22  thf('14', plain,
% 1.01/1.22      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.01/1.22         = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.01/1.22            (k2_zfmisc_1 @ sk_C @ sk_D_2)))),
% 1.01/1.22      inference('demod', [status(thm)], ['12', '13'])).
% 1.01/1.22  thf(t123_zfmisc_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.22     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 1.01/1.22       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 1.01/1.22  thf('15', plain,
% 1.01/1.22      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.01/1.22         ((k2_zfmisc_1 @ (k3_xboole_0 @ X45 @ X47) @ (k3_xboole_0 @ X46 @ X48))
% 1.01/1.22           = (k3_xboole_0 @ (k2_zfmisc_1 @ X45 @ X46) @ 
% 1.01/1.22              (k2_zfmisc_1 @ X47 @ X48)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.01/1.22  thf('16', plain,
% 1.01/1.22      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.01/1.22         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 1.01/1.22            (k3_xboole_0 @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('demod', [status(thm)], ['14', '15'])).
% 1.01/1.22  thf(t117_zfmisc_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.01/1.22          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 1.01/1.22            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 1.01/1.22          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 1.01/1.22  thf('17', plain,
% 1.01/1.22      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.01/1.22         (((X39) = (k1_xboole_0))
% 1.01/1.22          | (r1_tarski @ X40 @ X41)
% 1.01/1.22          | ~ (r1_tarski @ (k2_zfmisc_1 @ X39 @ X40) @ 
% 1.01/1.22               (k2_zfmisc_1 @ X39 @ X41)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.01/1.22  thf('18', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ X0) @ 
% 1.01/1.22             (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.01/1.22          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_B @ sk_D_2))
% 1.01/1.22          | ((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['16', '17'])).
% 1.01/1.22  thf('19', plain,
% 1.01/1.22      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 1.01/1.22        | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['7', '18'])).
% 1.01/1.22  thf('20', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.01/1.22      inference('sup+', [status(thm)], ['0', '4'])).
% 1.01/1.22  thf('21', plain,
% 1.01/1.22      (![X6 : $i, X8 : $i]:
% 1.01/1.22         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.01/1.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.01/1.22  thf('22', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.01/1.22          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['20', '21'])).
% 1.01/1.22  thf('23', plain,
% 1.01/1.22      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 1.01/1.22        | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['19', '22'])).
% 1.01/1.22  thf('24', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.01/1.22           = (k3_xboole_0 @ X21 @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.22  thf(t38_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 1.01/1.22       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.01/1.22  thf('25', plain,
% 1.01/1.22      (![X18 : $i, X19 : $i]:
% 1.01/1.22         (((X18) = (k1_xboole_0))
% 1.01/1.22          | ~ (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.01/1.22  thf('26', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.01/1.22          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['24', '25'])).
% 1.01/1.22  thf('27', plain,
% 1.01/1.22      ((~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_D_2) @ sk_B)
% 1.01/1.22        | ((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 1.01/1.22        | ((k4_xboole_0 @ sk_B @ sk_D_2) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['23', '26'])).
% 1.01/1.22  thf('28', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 1.01/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.22  thf('29', plain,
% 1.01/1.22      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 1.01/1.22        | ((k4_xboole_0 @ sk_B @ sk_D_2) = (k1_xboole_0)))),
% 1.01/1.22      inference('demod', [status(thm)], ['27', '28'])).
% 1.01/1.22  thf('30', plain,
% 1.01/1.22      (![X9 : $i, X10 : $i]:
% 1.01/1.22         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 1.01/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.01/1.22  thf('31', plain,
% 1.01/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.22        | ((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 1.01/1.22        | (r1_tarski @ sk_B @ sk_D_2))),
% 1.01/1.22      inference('sup-', [status(thm)], ['29', '30'])).
% 1.01/1.22  thf('32', plain,
% 1.01/1.22      (((r1_tarski @ sk_B @ sk_D_2)
% 1.01/1.22        | ((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.01/1.22      inference('simplify', [status(thm)], ['31'])).
% 1.01/1.22  thf('33', plain,
% 1.01/1.22      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D_2))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('34', plain,
% 1.01/1.22      ((~ (r1_tarski @ sk_B @ sk_D_2)) <= (~ ((r1_tarski @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('split', [status(esa)], ['33'])).
% 1.01/1.22  thf('35', plain,
% 1.01/1.22      ((((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))
% 1.01/1.22         <= (~ ((r1_tarski @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['32', '34'])).
% 1.01/1.22  thf('36', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.01/1.22      inference('simplify', [status(thm)], ['1'])).
% 1.01/1.22  thf('37', plain,
% 1.01/1.22      (((k2_zfmisc_1 @ sk_A @ sk_B)
% 1.01/1.22         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 1.01/1.22            (k3_xboole_0 @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('demod', [status(thm)], ['14', '15'])).
% 1.01/1.22  thf('38', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 1.01/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.01/1.22  thf('39', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.01/1.22           = (k3_xboole_0 @ X21 @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.22  thf('40', plain,
% 1.01/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['38', '39'])).
% 1.01/1.22  thf(t2_boole, axiom,
% 1.01/1.22    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.01/1.22  thf('41', plain,
% 1.01/1.22      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.22      inference('cnf', [status(esa)], [t2_boole])).
% 1.01/1.22  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('demod', [status(thm)], ['40', '41'])).
% 1.01/1.22  thf('43', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.01/1.22           = (k3_xboole_0 @ X21 @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.22  thf('44', plain,
% 1.01/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['42', '43'])).
% 1.01/1.22  thf('45', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 1.01/1.22      inference('cnf', [status(esa)], [t3_boole])).
% 1.01/1.22  thf('46', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['44', '45'])).
% 1.01/1.22  thf('47', plain,
% 1.01/1.22      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.01/1.22         ((k2_zfmisc_1 @ (k3_xboole_0 @ X45 @ X47) @ (k3_xboole_0 @ X46 @ X48))
% 1.01/1.22           = (k3_xboole_0 @ (k2_zfmisc_1 @ X45 @ X46) @ 
% 1.01/1.22              (k2_zfmisc_1 @ X47 @ X48)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 1.01/1.22  thf('48', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.01/1.22           = (k3_xboole_0 @ X21 @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.22  thf('49', plain,
% 1.01/1.22      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.01/1.22         ((r1_tarski @ X12 @ X13)
% 1.01/1.22          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X14)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.01/1.22  thf('50', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 1.01/1.22      inference('sup-', [status(thm)], ['48', '49'])).
% 1.01/1.22  thf('51', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X4 @ 
% 1.01/1.22             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 1.01/1.22          | (r1_tarski @ X4 @ (k2_zfmisc_1 @ X3 @ X1)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['47', '50'])).
% 1.01/1.22  thf('52', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X3 @ (k2_zfmisc_1 @ X0 @ (k3_xboole_0 @ X2 @ X1)))
% 1.01/1.22          | (r1_tarski @ X3 @ (k2_zfmisc_1 @ X0 @ X2)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['46', '51'])).
% 1.01/1.22  thf('53', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 1.01/1.22          | (r1_tarski @ X0 @ 
% 1.01/1.22             (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['37', '52'])).
% 1.01/1.22  thf('54', plain,
% 1.01/1.22      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.01/1.22        (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 1.01/1.22      inference('sup-', [status(thm)], ['36', '53'])).
% 1.01/1.22  thf('55', plain,
% 1.01/1.22      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.01/1.22         (((X39) = (k1_xboole_0))
% 1.01/1.22          | (r1_tarski @ X40 @ X41)
% 1.01/1.22          | ~ (r1_tarski @ (k2_zfmisc_1 @ X40 @ X39) @ 
% 1.01/1.22               (k2_zfmisc_1 @ X41 @ X39)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.01/1.22  thf('56', plain,
% 1.01/1.22      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C))
% 1.01/1.22        | ((sk_B) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['54', '55'])).
% 1.01/1.22  thf('57', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.01/1.22          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['20', '21'])).
% 1.01/1.22  thf('58', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['56', '57'])).
% 1.01/1.22  thf('59', plain,
% 1.01/1.22      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (~ ((r1_tarski @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['35', '58'])).
% 1.01/1.22  thf('60', plain,
% 1.01/1.22      ((~ (r1_tarski @ sk_B @ sk_D_2)) <= (~ ((r1_tarski @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('split', [status(esa)], ['33'])).
% 1.01/1.22  thf('61', plain,
% 1.01/1.22      (((~ (r1_tarski @ k1_xboole_0 @ sk_D_2) | ((sk_A) = (k1_xboole_0))))
% 1.01/1.22         <= (~ ((r1_tarski @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['59', '60'])).
% 1.01/1.22  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('demod', [status(thm)], ['40', '41'])).
% 1.01/1.22  thf('63', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 1.01/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.22  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.01/1.22      inference('sup+', [status(thm)], ['62', '63'])).
% 1.01/1.22  thf('65', plain,
% 1.01/1.22      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('demod', [status(thm)], ['61', '64'])).
% 1.01/1.22  thf('66', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('67', plain,
% 1.01/1.22      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 1.01/1.22         <= (~ ((r1_tarski @ sk_B @ sk_D_2)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['65', '66'])).
% 1.01/1.22  thf(d2_zfmisc_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.01/1.22       ( ![D:$i]:
% 1.01/1.22         ( ( r2_hidden @ D @ C ) <=>
% 1.01/1.22           ( ?[E:$i,F:$i]:
% 1.01/1.22             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 1.01/1.22               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 1.01/1.22  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 1.01/1.22  thf(zf_stmt_2, axiom,
% 1.01/1.22    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 1.01/1.22     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 1.01/1.22       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 1.01/1.22         ( r2_hidden @ E @ A ) ) ))).
% 1.01/1.22  thf(zf_stmt_3, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.01/1.22       ( ![D:$i]:
% 1.01/1.22         ( ( r2_hidden @ D @ C ) <=>
% 1.01/1.22           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 1.01/1.22  thf('68', plain,
% 1.01/1.22      (![X32 : $i, X33 : $i, X36 : $i]:
% 1.01/1.22         (((X36) = (k2_zfmisc_1 @ X33 @ X32))
% 1.01/1.22          | (zip_tseitin_0 @ (sk_F @ X36 @ X32 @ X33) @ 
% 1.01/1.22             (sk_E @ X36 @ X32 @ X33) @ (sk_D_1 @ X36 @ X32 @ X33) @ X32 @ X33)
% 1.01/1.22          | (r2_hidden @ (sk_D_1 @ X36 @ X32 @ X33) @ X36))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.22  thf('69', plain,
% 1.01/1.22      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.01/1.22         ((r2_hidden @ X24 @ X26)
% 1.01/1.22          | ~ (zip_tseitin_0 @ X24 @ X23 @ X25 @ X26 @ X27))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.01/1.22  thf('70', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.22         ((r2_hidden @ (sk_D_1 @ X2 @ X1 @ X0) @ X2)
% 1.01/1.22          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 1.01/1.22          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 1.01/1.22      inference('sup-', [status(thm)], ['68', '69'])).
% 1.01/1.22  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('demod', [status(thm)], ['40', '41'])).
% 1.01/1.22  thf(d5_xboole_0, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.01/1.22       ( ![D:$i]:
% 1.01/1.22         ( ( r2_hidden @ D @ C ) <=>
% 1.01/1.22           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.01/1.22  thf('72', plain,
% 1.01/1.22      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.01/1.22         (~ (r2_hidden @ X4 @ X3)
% 1.01/1.22          | ~ (r2_hidden @ X4 @ X2)
% 1.01/1.22          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.01/1.22      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.01/1.22  thf('73', plain,
% 1.01/1.22      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.01/1.22         (~ (r2_hidden @ X4 @ X2)
% 1.01/1.22          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.01/1.22      inference('simplify', [status(thm)], ['72'])).
% 1.01/1.22  thf('74', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['71', '73'])).
% 1.01/1.22  thf('75', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.01/1.22      inference('condensation', [status(thm)], ['74'])).
% 1.01/1.22  thf('76', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.01/1.22          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['70', '75'])).
% 1.01/1.22  thf('77', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.01/1.22      inference('condensation', [status(thm)], ['74'])).
% 1.01/1.22  thf('78', plain,
% 1.01/1.22      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['76', '77'])).
% 1.01/1.22  thf('79', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['56', '57'])).
% 1.01/1.22  thf('80', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.01/1.22          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['24', '25'])).
% 1.01/1.22  thf('81', plain,
% 1.01/1.22      ((~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_A)
% 1.01/1.22        | ((sk_B) = (k1_xboole_0))
% 1.01/1.22        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['79', '80'])).
% 1.01/1.22  thf('82', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 1.01/1.22      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.22  thf('83', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0))
% 1.01/1.22        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.01/1.22      inference('demod', [status(thm)], ['81', '82'])).
% 1.01/1.22  thf('84', plain,
% 1.01/1.22      (![X9 : $i, X10 : $i]:
% 1.01/1.22         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 1.01/1.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.01/1.22  thf('85', plain,
% 1.01/1.22      ((((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.22        | ((sk_B) = (k1_xboole_0))
% 1.01/1.22        | (r1_tarski @ sk_A @ sk_C))),
% 1.01/1.22      inference('sup-', [status(thm)], ['83', '84'])).
% 1.01/1.22  thf('86', plain, (((r1_tarski @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 1.01/1.22      inference('simplify', [status(thm)], ['85'])).
% 1.01/1.22  thf('87', plain,
% 1.01/1.22      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.01/1.22      inference('split', [status(esa)], ['33'])).
% 1.01/1.22  thf('88', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['86', '87'])).
% 1.01/1.22  thf('89', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('90', plain,
% 1.01/1.22      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.01/1.22         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['88', '89'])).
% 1.01/1.22  thf('91', plain,
% 1.01/1.22      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['78', '90'])).
% 1.01/1.22  thf('92', plain, (((r1_tarski @ sk_A @ sk_C))),
% 1.01/1.22      inference('simplify', [status(thm)], ['91'])).
% 1.01/1.22  thf('93', plain,
% 1.01/1.22      (~ ((r1_tarski @ sk_B @ sk_D_2)) | ~ ((r1_tarski @ sk_A @ sk_C))),
% 1.01/1.22      inference('split', [status(esa)], ['33'])).
% 1.01/1.22  thf('94', plain, (~ ((r1_tarski @ sk_B @ sk_D_2))),
% 1.01/1.22      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 1.01/1.22  thf('95', plain, (((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 1.01/1.22      inference('simpl_trail', [status(thm)], ['67', '94'])).
% 1.01/1.22  thf('96', plain,
% 1.01/1.22      (![X32 : $i, X33 : $i, X36 : $i]:
% 1.01/1.22         (((X36) = (k2_zfmisc_1 @ X33 @ X32))
% 1.01/1.22          | (zip_tseitin_0 @ (sk_F @ X36 @ X32 @ X33) @ 
% 1.01/1.22             (sk_E @ X36 @ X32 @ X33) @ (sk_D_1 @ X36 @ X32 @ X33) @ X32 @ X33)
% 1.01/1.22          | (r2_hidden @ (sk_D_1 @ X36 @ X32 @ X33) @ X36))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.22  thf('97', plain,
% 1.01/1.22      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.01/1.22         ((r2_hidden @ X23 @ X27)
% 1.01/1.22          | ~ (zip_tseitin_0 @ X24 @ X23 @ X25 @ X26 @ X27))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.01/1.22  thf('98', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.22         ((r2_hidden @ (sk_D_1 @ X2 @ X1 @ X0) @ X2)
% 1.01/1.22          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 1.01/1.22          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['96', '97'])).
% 1.01/1.22  thf('99', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.01/1.22      inference('condensation', [status(thm)], ['74'])).
% 1.01/1.22  thf('100', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 1.01/1.22          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['98', '99'])).
% 1.01/1.22  thf('101', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.01/1.22      inference('condensation', [status(thm)], ['74'])).
% 1.01/1.22  thf('102', plain,
% 1.01/1.22      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['100', '101'])).
% 1.01/1.22  thf('103', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.01/1.22      inference('demod', [status(thm)], ['95', '102'])).
% 1.01/1.22  thf('104', plain, ($false), inference('simplify', [status(thm)], ['103'])).
% 1.01/1.22  
% 1.01/1.22  % SZS output end Refutation
% 1.01/1.22  
% 1.01/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
