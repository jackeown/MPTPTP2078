%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HsaiFsa8Fd

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:10 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 101 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  432 ( 631 expanded)
%              Number of equality atoms :   39 (  61 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X35 ) @ X37 )
      | ~ ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ X13 @ X10 )
      | ( X12
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ X13 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( X12
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,(
    ! [X15: $i,X17: $i] :
      ( ( X15 = X17 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','41'])).

thf('43',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('46',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HsaiFsa8Fd
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 192 iterations in 0.138s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(d1_xboole_0, axiom,
% 0.38/0.59    (![A:$i]:
% 0.38/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.38/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.59  thf(t46_zfmisc_1, conjecture,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.59       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i]:
% 0.38/0.59        ( ( r2_hidden @ A @ B ) =>
% 0.38/0.59          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.38/0.59  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(l1_zfmisc_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.38/0.59  thf('2', plain,
% 0.38/0.59      (![X35 : $i, X37 : $i]:
% 0.38/0.59         ((r1_tarski @ (k1_tarski @ X35) @ X37) | ~ (r2_hidden @ X35 @ X37))),
% 0.38/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.59  thf('3', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.38/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.59  thf(t28_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.59  thf('4', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i]:
% 0.38/0.59         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.59  thf('5', plain,
% 0.38/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.38/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.59  thf(t100_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.59  thf('6', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X18 @ X19)
% 0.38/0.59           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('7', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.38/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.59  thf(d10_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.59  thf('8', plain,
% 0.38/0.59      (![X15 : $i, X16 : $i]: ((r1_tarski @ X15 @ X16) | ((X15) != (X16)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.59  thf('9', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 0.38/0.59      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.59  thf('10', plain,
% 0.38/0.59      (![X21 : $i, X22 : $i]:
% 0.38/0.59         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.38/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.59  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.59  thf('12', plain,
% 0.38/0.59      (![X18 : $i, X19 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X18 @ X19)
% 0.38/0.59           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.38/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.59  thf('13', plain,
% 0.38/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.59  thf(d5_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i]:
% 0.38/0.59     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.38/0.59       ( ![D:$i]:
% 0.38/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.59           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.38/0.59  thf('14', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X13 @ X12)
% 0.38/0.59          | (r2_hidden @ X13 @ X10)
% 0.38/0.59          | ((X12) != (k4_xboole_0 @ X10 @ X11)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.59  thf('15', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.38/0.59         ((r2_hidden @ X13 @ X10)
% 0.38/0.59          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.59  thf('16', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['13', '15'])).
% 0.38/0.59  thf('17', plain,
% 0.38/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.59  thf('18', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X13 @ X12)
% 0.38/0.59          | ~ (r2_hidden @ X13 @ X11)
% 0.38/0.59          | ((X12) != (k4_xboole_0 @ X10 @ X11)))),
% 0.38/0.59      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.59  thf('19', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X13 @ X11)
% 0.38/0.59          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.59  thf('20', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.38/0.59          | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['17', '19'])).
% 0.38/0.59  thf('21', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.59      inference('clc', [status(thm)], ['16', '20'])).
% 0.38/0.59  thf('22', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['7', '21'])).
% 0.38/0.59  thf('23', plain,
% 0.38/0.59      ((v1_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.38/0.59      inference('sup-', [status(thm)], ['0', '22'])).
% 0.38/0.59  thf(d3_tarski, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.59  thf('24', plain,
% 0.38/0.59      (![X6 : $i, X8 : $i]:
% 0.38/0.59         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf('25', plain,
% 0.38/0.59      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.38/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.59  thf('26', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.59  thf('27', plain,
% 0.38/0.59      (![X6 : $i, X8 : $i]:
% 0.38/0.59         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.38/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.59  thf('28', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.59  thf(t1_boole, axiom,
% 0.38/0.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.59  thf('29', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.59  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.59  thf(t39_xboole_1, axiom,
% 0.38/0.59    (![A:$i,B:$i]:
% 0.38/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.59  thf('31', plain,
% 0.38/0.59      (![X23 : $i, X24 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.38/0.59           = (k2_xboole_0 @ X23 @ X24))),
% 0.38/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.59  thf('32', plain,
% 0.38/0.59      (![X0 : $i]:
% 0.38/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.59  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.59      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.59  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.59  thf('35', plain,
% 0.38/0.59      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X13 @ X11)
% 0.38/0.59          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.38/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.59  thf('36', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]:
% 0.38/0.59         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.59  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.59      inference('condensation', [status(thm)], ['36'])).
% 0.38/0.59  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.59      inference('sup-', [status(thm)], ['27', '37'])).
% 0.38/0.59  thf('39', plain,
% 0.38/0.59      (![X15 : $i, X17 : $i]:
% 0.38/0.59         (((X15) = (X17))
% 0.38/0.59          | ~ (r1_tarski @ X17 @ X15)
% 0.38/0.59          | ~ (r1_tarski @ X15 @ X17))),
% 0.38/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.59  thf('40', plain,
% 0.38/0.59      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.59  thf('41', plain,
% 0.38/0.59      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.59      inference('sup-', [status(thm)], ['26', '40'])).
% 0.38/0.59  thf('42', plain,
% 0.38/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.38/0.59      inference('sup-', [status(thm)], ['23', '41'])).
% 0.38/0.59  thf('43', plain,
% 0.38/0.59      (![X23 : $i, X24 : $i]:
% 0.38/0.59         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.38/0.59           = (k2_xboole_0 @ X23 @ X24))),
% 0.38/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.59  thf('44', plain,
% 0.38/0.59      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.38/0.59         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('sup+', [status(thm)], ['42', '43'])).
% 0.38/0.59  thf('45', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.38/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.59  thf('46', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.38/0.59      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.59  thf('47', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf('48', plain,
% 0.38/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.59  thf('49', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.38/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.59  thf('50', plain, ($false),
% 0.38/0.59      inference('simplify_reflect-', [status(thm)], ['46', '49'])).
% 0.38/0.59  
% 0.38/0.59  % SZS output end Refutation
% 0.38/0.59  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
