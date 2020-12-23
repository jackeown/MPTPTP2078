%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zGlch4zKry

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:46 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   69 (  92 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  466 ( 639 expanded)
%              Number of equality atoms :   37 (  55 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t81_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( ( k4_xboole_0 @ X42 @ ( k1_tarski @ X41 ) )
       != X42 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','28'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X44 ) @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('36',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X44 ) @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ( r1_tarski @ ( k2_xboole_0 @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zGlch4zKry
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.80/2.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.80/2.02  % Solved by: fo/fo7.sh
% 1.80/2.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/2.02  % done 3984 iterations in 1.561s
% 1.80/2.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.80/2.02  % SZS output start Refutation
% 1.80/2.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.80/2.02  thf(sk_A_type, type, sk_A: $i).
% 1.80/2.02  thf(sk_B_type, type, sk_B: $i > $i).
% 1.80/2.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.80/2.02  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.80/2.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.80/2.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.80/2.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.80/2.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.80/2.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.80/2.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.80/2.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.80/2.02  thf(t81_zfmisc_1, conjecture,
% 1.80/2.02    (![A:$i,B:$i]:
% 1.80/2.02     ( r1_tarski @
% 1.80/2.02       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 1.80/2.02       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.80/2.02  thf(zf_stmt_0, negated_conjecture,
% 1.80/2.02    (~( ![A:$i,B:$i]:
% 1.80/2.02        ( r1_tarski @
% 1.80/2.02          ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 1.80/2.02          ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.80/2.02    inference('cnf.neg', [status(esa)], [t81_zfmisc_1])).
% 1.80/2.02  thf('0', plain,
% 1.80/2.02      (~ (r1_tarski @ 
% 1.80/2.02          (k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B_1)) @ 
% 1.80/2.02          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B_1)))),
% 1.80/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.02  thf(t7_xboole_0, axiom,
% 1.80/2.02    (![A:$i]:
% 1.80/2.02     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.80/2.02          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.80/2.02  thf('1', plain,
% 1.80/2.02      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.80/2.02      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.80/2.02  thf(t3_boole, axiom,
% 1.80/2.02    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.80/2.02  thf('2', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.80/2.02      inference('cnf', [status(esa)], [t3_boole])).
% 1.80/2.02  thf(t48_xboole_1, axiom,
% 1.80/2.02    (![A:$i,B:$i]:
% 1.80/2.02     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.80/2.02  thf('3', plain,
% 1.80/2.02      (![X14 : $i, X15 : $i]:
% 1.80/2.02         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.80/2.02           = (k3_xboole_0 @ X14 @ X15))),
% 1.80/2.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.80/2.02  thf('4', plain,
% 1.80/2.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.80/2.02      inference('sup+', [status(thm)], ['2', '3'])).
% 1.80/2.02  thf(d4_xboole_0, axiom,
% 1.80/2.02    (![A:$i,B:$i,C:$i]:
% 1.80/2.02     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.80/2.02       ( ![D:$i]:
% 1.80/2.02         ( ( r2_hidden @ D @ C ) <=>
% 1.80/2.02           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.80/2.02  thf('5', plain,
% 1.80/2.02      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.80/2.02         (~ (r2_hidden @ X4 @ X3)
% 1.80/2.02          | (r2_hidden @ X4 @ X2)
% 1.80/2.02          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.80/2.02      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.80/2.02  thf('6', plain,
% 1.80/2.02      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.80/2.02         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.80/2.02      inference('simplify', [status(thm)], ['5'])).
% 1.80/2.02  thf('7', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 1.80/2.02          | (r2_hidden @ X1 @ k1_xboole_0))),
% 1.80/2.02      inference('sup-', [status(thm)], ['4', '6'])).
% 1.80/2.02  thf(t4_boole, axiom,
% 1.80/2.02    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.80/2.02  thf('8', plain,
% 1.80/2.02      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 1.80/2.02      inference('cnf', [status(esa)], [t4_boole])).
% 1.80/2.02  thf(t65_zfmisc_1, axiom,
% 1.80/2.02    (![A:$i,B:$i]:
% 1.80/2.02     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.80/2.02       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.80/2.02  thf('9', plain,
% 1.80/2.02      (![X41 : $i, X42 : $i]:
% 1.80/2.02         (~ (r2_hidden @ X41 @ X42)
% 1.80/2.02          | ((k4_xboole_0 @ X42 @ (k1_tarski @ X41)) != (X42)))),
% 1.80/2.02      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.80/2.02  thf('10', plain,
% 1.80/2.02      (![X0 : $i]:
% 1.80/2.02         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 1.80/2.02      inference('sup-', [status(thm)], ['8', '9'])).
% 1.80/2.02  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.80/2.02      inference('simplify', [status(thm)], ['10'])).
% 1.80/2.02  thf('12', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 1.80/2.02      inference('clc', [status(thm)], ['7', '11'])).
% 1.80/2.02  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.02      inference('sup-', [status(thm)], ['1', '12'])).
% 1.80/2.02  thf(t41_xboole_1, axiom,
% 1.80/2.02    (![A:$i,B:$i,C:$i]:
% 1.80/2.02     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.80/2.02       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.80/2.02  thf('14', plain,
% 1.80/2.02      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.80/2.02         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.80/2.02           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.80/2.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.80/2.02  thf('15', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         ((k1_xboole_0)
% 1.80/2.02           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.80/2.02      inference('sup+', [status(thm)], ['13', '14'])).
% 1.80/2.02  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.02      inference('sup-', [status(thm)], ['1', '12'])).
% 1.80/2.02  thf('17', plain,
% 1.80/2.02      (![X14 : $i, X15 : $i]:
% 1.80/2.02         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.80/2.02           = (k3_xboole_0 @ X14 @ X15))),
% 1.80/2.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.80/2.02  thf('18', plain,
% 1.80/2.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.80/2.02      inference('sup+', [status(thm)], ['16', '17'])).
% 1.80/2.02  thf('19', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.80/2.02      inference('cnf', [status(esa)], [t3_boole])).
% 1.80/2.02  thf('20', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.80/2.02      inference('demod', [status(thm)], ['18', '19'])).
% 1.80/2.02  thf(t53_xboole_1, axiom,
% 1.80/2.02    (![A:$i,B:$i,C:$i]:
% 1.80/2.02     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.80/2.02       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.80/2.02  thf('21', plain,
% 1.80/2.02      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.80/2.02         ((k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 1.80/2.02           = (k3_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ 
% 1.80/2.02              (k4_xboole_0 @ X17 @ X19)))),
% 1.80/2.02      inference('cnf', [status(esa)], [t53_xboole_1])).
% 1.80/2.02  thf('22', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 1.80/2.02           = (k4_xboole_0 @ X1 @ X0))),
% 1.80/2.02      inference('sup+', [status(thm)], ['20', '21'])).
% 1.80/2.02  thf('23', plain,
% 1.80/2.02      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.80/2.02         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.80/2.02           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.80/2.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.80/2.02  thf(t98_xboole_1, axiom,
% 1.80/2.02    (![A:$i,B:$i]:
% 1.80/2.02     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.80/2.02  thf('24', plain,
% 1.80/2.02      (![X25 : $i, X26 : $i]:
% 1.80/2.02         ((k2_xboole_0 @ X25 @ X26)
% 1.80/2.02           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 1.80/2.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.80/2.02  thf('25', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 1.80/2.02           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.80/2.02      inference('sup+', [status(thm)], ['23', '24'])).
% 1.80/2.02  thf('26', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.80/2.02           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.80/2.02      inference('sup+', [status(thm)], ['22', '25'])).
% 1.80/2.02  thf('27', plain,
% 1.80/2.02      (![X25 : $i, X26 : $i]:
% 1.80/2.02         ((k2_xboole_0 @ X25 @ X26)
% 1.80/2.02           = (k5_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25)))),
% 1.80/2.02      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.80/2.02  thf('28', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.80/2.02           = (k2_xboole_0 @ X0 @ X1))),
% 1.80/2.02      inference('demod', [status(thm)], ['26', '27'])).
% 1.80/2.02  thf('29', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.80/2.02      inference('demod', [status(thm)], ['15', '28'])).
% 1.80/2.02  thf(l32_xboole_1, axiom,
% 1.80/2.02    (![A:$i,B:$i]:
% 1.80/2.02     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.80/2.02  thf('30', plain,
% 1.80/2.02      (![X7 : $i, X8 : $i]:
% 1.80/2.02         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 1.80/2.02      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.80/2.02  thf('31', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         (((k1_xboole_0) != (k1_xboole_0))
% 1.80/2.02          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.80/2.02      inference('sup-', [status(thm)], ['29', '30'])).
% 1.80/2.02  thf('32', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.80/2.02      inference('simplify', [status(thm)], ['31'])).
% 1.80/2.02  thf(t79_zfmisc_1, axiom,
% 1.80/2.02    (![A:$i,B:$i]:
% 1.80/2.02     ( ( r1_tarski @ A @ B ) =>
% 1.80/2.02       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.80/2.02  thf('33', plain,
% 1.80/2.02      (![X44 : $i, X45 : $i]:
% 1.80/2.02         ((r1_tarski @ (k1_zfmisc_1 @ X44) @ (k1_zfmisc_1 @ X45))
% 1.80/2.02          | ~ (r1_tarski @ X44 @ X45))),
% 1.80/2.02      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.80/2.02  thf('34', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 1.80/2.02          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.80/2.02      inference('sup-', [status(thm)], ['32', '33'])).
% 1.80/2.02  thf(t7_xboole_1, axiom,
% 1.80/2.02    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.80/2.02  thf('35', plain,
% 1.80/2.02      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.80/2.02      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.80/2.02  thf('36', plain,
% 1.80/2.02      (![X44 : $i, X45 : $i]:
% 1.80/2.02         ((r1_tarski @ (k1_zfmisc_1 @ X44) @ (k1_zfmisc_1 @ X45))
% 1.80/2.02          | ~ (r1_tarski @ X44 @ X45))),
% 1.80/2.02      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.80/2.02  thf('37', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 1.80/2.02          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.80/2.02      inference('sup-', [status(thm)], ['35', '36'])).
% 1.80/2.02  thf(t8_xboole_1, axiom,
% 1.80/2.02    (![A:$i,B:$i,C:$i]:
% 1.80/2.02     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.80/2.02       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.80/2.02  thf('38', plain,
% 1.80/2.02      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.80/2.02         (~ (r1_tarski @ X22 @ X23)
% 1.80/2.02          | ~ (r1_tarski @ X24 @ X23)
% 1.80/2.02          | (r1_tarski @ (k2_xboole_0 @ X22 @ X24) @ X23))),
% 1.80/2.02      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.80/2.02  thf('39', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.02         ((r1_tarski @ (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 1.80/2.02           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.80/2.02          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.80/2.02      inference('sup-', [status(thm)], ['37', '38'])).
% 1.80/2.02  thf('40', plain,
% 1.80/2.02      (![X0 : $i, X1 : $i]:
% 1.80/2.02         (r1_tarski @ 
% 1.80/2.02          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 1.80/2.02          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.80/2.02      inference('sup-', [status(thm)], ['34', '39'])).
% 1.80/2.02  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 1.80/2.02  
% 1.80/2.02  % SZS output end Refutation
% 1.80/2.02  
% 1.80/2.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
