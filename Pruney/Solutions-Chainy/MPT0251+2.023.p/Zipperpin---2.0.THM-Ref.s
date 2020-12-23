%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r9jqpmtNXX

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 127 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  482 ( 806 expanded)
%              Number of equality atoms :   45 (  80 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
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
    ! [X42: $i,X44: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X42 ) @ X44 )
      | ~ ( r2_hidden @ X42 @ X44 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
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

thf('24',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X31 @ X30 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','38'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('44',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','47'])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('55',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r9jqpmtNXX
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 136 iterations in 0.063s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(d1_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf(t46_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.52       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( r2_hidden @ A @ B ) =>
% 0.20/0.52          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.20/0.52  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(l1_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X42 : $i, X44 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X42) @ X44) | ~ (r2_hidden @ X42 @ X44))),
% 0.20/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.52  thf('3', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(t28_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X20 @ X21)
% 0.20/0.52           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.20/0.52         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('9', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.20/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X20 @ X21)
% 0.20/0.52           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf(d5_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X11 @ X10)
% 0.20/0.52          | (r2_hidden @ X11 @ X8)
% 0.20/0.52          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.52         ((r2_hidden @ X11 @ X8)
% 0.20/0.52          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X11 @ X10)
% 0.20/0.52          | ~ (r2_hidden @ X11 @ X9)
% 0.20/0.52          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X11 @ X9)
% 0.20/0.52          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.52          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['16', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((v1_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf(commutativity_k2_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X30 : $i, X31 : $i]:
% 0.20/0.52         ((k2_tarski @ X31 @ X30) = (k2_tarski @ X30 @ X31))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.52  thf(l51_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X45 : $i, X46 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X45 : $i, X46 : $i]:
% 0.20/0.52         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.20/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf(t1_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('30', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.52  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf(t39_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.20/0.52           = (k2_xboole_0 @ X25 @ X26))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X11 @ X9)
% 0.20/0.52          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('condensation', [status(thm)], ['37'])).
% 0.20/0.52  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '38'])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X4 : $i, X6 : $i]:
% 0.20/0.52         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X17 : $i, X19 : $i]:
% 0.20/0.52         (((X17) = (X19))
% 0.20/0.52          | ~ (r1_tarski @ X19 @ X17)
% 0.20/0.52          | ~ (r1_tarski @ X17 @ X19))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.20/0.52           = (k2_xboole_0 @ X25 @ X26))),
% 0.20/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.20/0.52         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['48', '49'])).
% 0.20/0.52  thf('51', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.52  thf('52', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('53', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('55', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.20/0.52      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('56', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['52', '55'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
