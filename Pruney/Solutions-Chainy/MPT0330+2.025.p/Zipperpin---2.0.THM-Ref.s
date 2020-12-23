%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fMVKhJd4AJ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:02 EST 2020

% Result     : Theorem 15.56s
% Output     : Refutation 15.56s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 166 expanded)
%              Number of leaves         :   20 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  598 (1330 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t143_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
        & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
          & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
       => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( k2_zfmisc_1 @ X23 @ ( k2_xboole_0 @ X20 @ X22 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X20 ) @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ),
    inference('sup+',[status(thm)],['2','16'])).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X2 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ sk_C ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['1','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('40',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','50'])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','50'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['32','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fMVKhJd4AJ
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.56/15.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.56/15.76  % Solved by: fo/fo7.sh
% 15.56/15.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.56/15.76  % done 12448 iterations in 15.299s
% 15.56/15.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.56/15.76  % SZS output start Refutation
% 15.56/15.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 15.56/15.76  thf(sk_B_type, type, sk_B: $i).
% 15.56/15.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 15.56/15.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.56/15.76  thf(sk_E_type, type, sk_E: $i).
% 15.56/15.76  thf(sk_F_type, type, sk_F: $i).
% 15.56/15.76  thf(sk_C_type, type, sk_C: $i).
% 15.56/15.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 15.56/15.76  thf(sk_A_type, type, sk_A: $i).
% 15.56/15.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.56/15.76  thf(sk_D_type, type, sk_D: $i).
% 15.56/15.76  thf(t143_zfmisc_1, conjecture,
% 15.56/15.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 15.56/15.76     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 15.56/15.76         ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 15.56/15.76       ( r1_tarski @
% 15.56/15.76         ( k2_xboole_0 @ A @ B ) @ 
% 15.56/15.76         ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ))).
% 15.56/15.76  thf(zf_stmt_0, negated_conjecture,
% 15.56/15.76    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 15.56/15.76        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 15.56/15.76            ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 15.56/15.76          ( r1_tarski @
% 15.56/15.76            ( k2_xboole_0 @ A @ B ) @ 
% 15.56/15.76            ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )),
% 15.56/15.76    inference('cnf.neg', [status(esa)], [t143_zfmisc_1])).
% 15.56/15.76  thf('0', plain,
% 15.56/15.76      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 15.56/15.76          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 15.56/15.76           (k2_xboole_0 @ sk_D @ sk_F)))),
% 15.56/15.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.76  thf(t120_zfmisc_1, axiom,
% 15.56/15.76    (![A:$i,B:$i,C:$i]:
% 15.56/15.76     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 15.56/15.76         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 15.56/15.76       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 15.56/15.76         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 15.56/15.76  thf('1', plain,
% 15.56/15.76      (![X20 : $i, X22 : $i, X23 : $i]:
% 15.56/15.76         ((k2_zfmisc_1 @ X23 @ (k2_xboole_0 @ X20 @ X22))
% 15.56/15.76           = (k2_xboole_0 @ (k2_zfmisc_1 @ X23 @ X20) @ 
% 15.56/15.76              (k2_zfmisc_1 @ X23 @ X22)))),
% 15.56/15.76      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 15.56/15.76  thf('2', plain,
% 15.56/15.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 15.56/15.76         ((k2_zfmisc_1 @ (k2_xboole_0 @ X20 @ X22) @ X21)
% 15.56/15.76           = (k2_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 15.56/15.76              (k2_zfmisc_1 @ X22 @ X21)))),
% 15.56/15.76      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 15.56/15.76  thf('3', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 15.56/15.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.76  thf(l32_xboole_1, axiom,
% 15.56/15.76    (![A:$i,B:$i]:
% 15.56/15.76     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 15.56/15.76  thf('4', plain,
% 15.56/15.76      (![X3 : $i, X5 : $i]:
% 15.56/15.76         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 15.56/15.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 15.56/15.76  thf('5', plain,
% 15.56/15.76      (((k4_xboole_0 @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F)) = (k1_xboole_0))),
% 15.56/15.76      inference('sup-', [status(thm)], ['3', '4'])).
% 15.56/15.76  thf(t41_xboole_1, axiom,
% 15.56/15.76    (![A:$i,B:$i,C:$i]:
% 15.56/15.76     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 15.56/15.76       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 15.56/15.76  thf('6', plain,
% 15.56/15.76      (![X15 : $i, X16 : $i, X17 : $i]:
% 15.56/15.76         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 15.56/15.76           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 15.56/15.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.56/15.76  thf('7', plain,
% 15.56/15.76      (![X3 : $i, X4 : $i]:
% 15.56/15.76         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 15.56/15.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 15.56/15.76  thf('8', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.76         (((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 15.56/15.76          | (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.56/15.76      inference('sup-', [status(thm)], ['6', '7'])).
% 15.56/15.76  thf('9', plain,
% 15.56/15.76      (![X0 : $i]:
% 15.56/15.76         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 15.56/15.76          | (r1_tarski @ sk_B @ 
% 15.56/15.76             (k2_xboole_0 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0)))),
% 15.56/15.76      inference('sup-', [status(thm)], ['5', '8'])).
% 15.56/15.76  thf(t36_xboole_1, axiom,
% 15.56/15.76    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 15.56/15.76  thf('10', plain,
% 15.56/15.76      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 15.56/15.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.56/15.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 15.56/15.76  thf('11', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 15.56/15.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.56/15.76  thf(d10_xboole_0, axiom,
% 15.56/15.76    (![A:$i,B:$i]:
% 15.56/15.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 15.56/15.76  thf('12', plain,
% 15.56/15.76      (![X0 : $i, X2 : $i]:
% 15.56/15.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.56/15.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.56/15.76  thf('13', plain,
% 15.56/15.76      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 15.56/15.76      inference('sup-', [status(thm)], ['11', '12'])).
% 15.56/15.76  thf('14', plain,
% 15.56/15.76      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.56/15.76      inference('sup-', [status(thm)], ['10', '13'])).
% 15.56/15.76  thf('15', plain,
% 15.56/15.76      (![X0 : $i]:
% 15.56/15.76         (((k1_xboole_0) != (k1_xboole_0))
% 15.56/15.76          | (r1_tarski @ sk_B @ 
% 15.56/15.76             (k2_xboole_0 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0)))),
% 15.56/15.76      inference('demod', [status(thm)], ['9', '14'])).
% 15.56/15.76  thf('16', plain,
% 15.56/15.76      (![X0 : $i]:
% 15.56/15.76         (r1_tarski @ sk_B @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_E @ sk_F) @ X0))),
% 15.56/15.76      inference('simplify', [status(thm)], ['15'])).
% 15.56/15.76  thf('17', plain,
% 15.56/15.76      (![X0 : $i]:
% 15.56/15.76         (r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F))),
% 15.56/15.76      inference('sup+', [status(thm)], ['2', '16'])).
% 15.56/15.76  thf('18', plain,
% 15.56/15.76      (![X20 : $i, X21 : $i, X22 : $i]:
% 15.56/15.76         ((k2_zfmisc_1 @ (k2_xboole_0 @ X20 @ X22) @ X21)
% 15.56/15.76           = (k2_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ 
% 15.56/15.76              (k2_zfmisc_1 @ X22 @ X21)))),
% 15.56/15.76      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 15.56/15.76  thf('19', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 15.56/15.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.56/15.76  thf('20', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 15.56/15.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.56/15.76  thf(t13_xboole_1, axiom,
% 15.56/15.76    (![A:$i,B:$i,C:$i,D:$i]:
% 15.56/15.76     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 15.56/15.76       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 15.56/15.76  thf('21', plain,
% 15.56/15.76      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 15.56/15.76         (~ (r1_tarski @ X8 @ X9)
% 15.56/15.76          | ~ (r1_tarski @ X10 @ X11)
% 15.56/15.76          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ (k2_xboole_0 @ X9 @ X11)))),
% 15.56/15.76      inference('cnf', [status(esa)], [t13_xboole_1])).
% 15.56/15.76  thf('22', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.76         ((r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X2) @ 
% 15.56/15.76           (k2_xboole_0 @ X0 @ X1))
% 15.56/15.76          | ~ (r1_tarski @ X2 @ X1))),
% 15.56/15.76      inference('sup-', [status(thm)], ['20', '21'])).
% 15.56/15.76  thf('23', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 15.56/15.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 15.56/15.76  thf(t12_xboole_1, axiom,
% 15.56/15.76    (![A:$i,B:$i]:
% 15.56/15.76     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 15.56/15.76  thf('24', plain,
% 15.56/15.76      (![X6 : $i, X7 : $i]:
% 15.56/15.76         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 15.56/15.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 15.56/15.76  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 15.56/15.76      inference('sup-', [status(thm)], ['23', '24'])).
% 15.56/15.76  thf('26', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.76         ((r1_tarski @ X2 @ (k2_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X2 @ X1))),
% 15.56/15.76      inference('demod', [status(thm)], ['22', '25'])).
% 15.56/15.76  thf('27', plain,
% 15.56/15.76      (![X0 : $i]:
% 15.56/15.76         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 15.56/15.76      inference('sup-', [status(thm)], ['19', '26'])).
% 15.56/15.76  thf('28', plain,
% 15.56/15.76      (![X0 : $i]:
% 15.56/15.76         (r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 15.56/15.76      inference('sup+', [status(thm)], ['18', '27'])).
% 15.56/15.76  thf('29', plain,
% 15.56/15.76      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 15.56/15.76         (~ (r1_tarski @ X8 @ X9)
% 15.56/15.76          | ~ (r1_tarski @ X10 @ X11)
% 15.56/15.76          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ (k2_xboole_0 @ X9 @ X11)))),
% 15.56/15.76      inference('cnf', [status(esa)], [t13_xboole_1])).
% 15.56/15.76  thf('30', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.76         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X2) @ 
% 15.56/15.76           (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D) @ X1))
% 15.56/15.76          | ~ (r1_tarski @ X2 @ X1))),
% 15.56/15.76      inference('sup-', [status(thm)], ['28', '29'])).
% 15.56/15.76  thf('31', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]:
% 15.56/15.76         (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 15.56/15.76          (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_C) @ sk_D) @ 
% 15.56/15.76           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F)))),
% 15.56/15.76      inference('sup-', [status(thm)], ['17', '30'])).
% 15.56/15.76  thf('32', plain,
% 15.56/15.76      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 15.56/15.76        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ sk_C) @ 
% 15.56/15.76         (k2_xboole_0 @ sk_D @ sk_F)))),
% 15.56/15.76      inference('sup+', [status(thm)], ['1', '31'])).
% 15.56/15.76  thf('33', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 15.56/15.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.56/15.76  thf('34', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 15.56/15.76      inference('simplify', [status(thm)], ['33'])).
% 15.56/15.76  thf('35', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.76         ((r1_tarski @ X2 @ (k2_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X2 @ X1))),
% 15.56/15.76      inference('demod', [status(thm)], ['22', '25'])).
% 15.56/15.76  thf('36', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 15.56/15.76      inference('sup-', [status(thm)], ['34', '35'])).
% 15.56/15.76  thf('37', plain,
% 15.56/15.76      (![X6 : $i, X7 : $i]:
% 15.56/15.76         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 15.56/15.76      inference('cnf', [status(esa)], [t12_xboole_1])).
% 15.56/15.76  thf('38', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]:
% 15.56/15.76         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 15.56/15.76           = (k2_xboole_0 @ X1 @ X0))),
% 15.56/15.76      inference('sup-', [status(thm)], ['36', '37'])).
% 15.56/15.76  thf('39', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 15.56/15.76      inference('simplify', [status(thm)], ['33'])).
% 15.56/15.76  thf('40', plain,
% 15.56/15.76      (![X3 : $i, X5 : $i]:
% 15.56/15.76         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 15.56/15.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 15.56/15.76  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.56/15.76      inference('sup-', [status(thm)], ['39', '40'])).
% 15.56/15.76  thf('42', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.76         (((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 15.56/15.76          | (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.56/15.76      inference('sup-', [status(thm)], ['6', '7'])).
% 15.56/15.76  thf('43', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]:
% 15.56/15.76         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 15.56/15.76          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.56/15.76      inference('sup-', [status(thm)], ['41', '42'])).
% 15.56/15.76  thf('44', plain,
% 15.56/15.76      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.56/15.76      inference('sup-', [status(thm)], ['10', '13'])).
% 15.56/15.76  thf('45', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]:
% 15.56/15.76         (((k1_xboole_0) != (k1_xboole_0))
% 15.56/15.76          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.56/15.76      inference('demod', [status(thm)], ['43', '44'])).
% 15.56/15.76  thf('46', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 15.56/15.76      inference('simplify', [status(thm)], ['45'])).
% 15.56/15.76  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 15.56/15.76      inference('simplify', [status(thm)], ['33'])).
% 15.56/15.76  thf('48', plain,
% 15.56/15.76      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 15.56/15.76         (~ (r1_tarski @ X8 @ X9)
% 15.56/15.76          | ~ (r1_tarski @ X10 @ X11)
% 15.56/15.76          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ (k2_xboole_0 @ X9 @ X11)))),
% 15.56/15.76      inference('cnf', [status(esa)], [t13_xboole_1])).
% 15.56/15.76  thf('49', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.76         ((r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X0 @ X1))
% 15.56/15.76          | ~ (r1_tarski @ X2 @ X1))),
% 15.56/15.76      inference('sup-', [status(thm)], ['47', '48'])).
% 15.56/15.76  thf('50', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.56/15.76         (r1_tarski @ (k2_xboole_0 @ X2 @ X1) @ 
% 15.56/15.76          (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.56/15.76      inference('sup-', [status(thm)], ['46', '49'])).
% 15.56/15.76  thf('51', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]:
% 15.56/15.76         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 15.56/15.76      inference('sup+', [status(thm)], ['38', '50'])).
% 15.56/15.76  thf('52', plain,
% 15.56/15.76      (![X0 : $i, X2 : $i]:
% 15.56/15.76         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 15.56/15.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 15.56/15.76  thf('53', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]:
% 15.56/15.76         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 15.56/15.76          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 15.56/15.76      inference('sup-', [status(thm)], ['51', '52'])).
% 15.56/15.76  thf('54', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]:
% 15.56/15.76         (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 15.56/15.76      inference('sup+', [status(thm)], ['38', '50'])).
% 15.56/15.76  thf('55', plain,
% 15.56/15.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.56/15.76      inference('demod', [status(thm)], ['53', '54'])).
% 15.56/15.76  thf('56', plain,
% 15.56/15.76      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 15.56/15.76        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 15.56/15.76         (k2_xboole_0 @ sk_D @ sk_F)))),
% 15.56/15.76      inference('demod', [status(thm)], ['32', '55'])).
% 15.56/15.76  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 15.56/15.76  
% 15.56/15.76  % SZS output end Refutation
% 15.56/15.76  
% 15.56/15.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
