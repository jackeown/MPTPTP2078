%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wH1c1XMXW5

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:30 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 102 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  415 ( 742 expanded)
%              Number of equality atoms :   32 (  55 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t79_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) ),
    inference('cnf.neg',[status(esa)],[t79_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('17',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('34',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wH1c1XMXW5
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.91/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.08  % Solved by: fo/fo7.sh
% 0.91/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.08  % done 1533 iterations in 0.638s
% 0.91/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.08  % SZS output start Refutation
% 0.91/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.08  thf(t79_xboole_1, conjecture,
% 0.91/1.08    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.91/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.08    (~( ![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )),
% 0.91/1.08    inference('cnf.neg', [status(esa)], [t79_xboole_1])).
% 0.91/1.08  thf('0', plain, (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.91/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.08  thf(t3_boole, axiom,
% 0.91/1.08    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.08  thf('1', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.08  thf(t36_xboole_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.91/1.08  thf('2', plain,
% 0.91/1.08      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.91/1.08      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.91/1.08  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.91/1.08      inference('sup+', [status(thm)], ['1', '2'])).
% 0.91/1.08  thf(t12_xboole_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.08  thf('4', plain,
% 0.91/1.08      (![X11 : $i, X12 : $i]:
% 0.91/1.08         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.91/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.08  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.08  thf(t48_xboole_1, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.91/1.08  thf('6', plain,
% 0.91/1.08      (![X19 : $i, X20 : $i]:
% 0.91/1.08         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.91/1.08           = (k3_xboole_0 @ X19 @ X20))),
% 0.91/1.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.08  thf(t41_xboole_1, axiom,
% 0.91/1.08    (![A:$i,B:$i,C:$i]:
% 0.91/1.08     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.08       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.91/1.08  thf('7', plain,
% 0.91/1.08      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.08         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.91/1.08           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.91/1.08      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.91/1.08  thf('8', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.91/1.08           = (k4_xboole_0 @ X2 @ 
% 0.91/1.08              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.91/1.08      inference('sup+', [status(thm)], ['6', '7'])).
% 0.91/1.08  thf('9', plain,
% 0.91/1.08      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.08         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.91/1.08           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.91/1.08      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.91/1.08  thf('10', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.91/1.08           = (k4_xboole_0 @ X2 @ 
% 0.91/1.08              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.91/1.08      inference('demod', [status(thm)], ['8', '9'])).
% 0.91/1.08  thf('11', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.91/1.08           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.91/1.08      inference('sup+', [status(thm)], ['5', '10'])).
% 0.91/1.08  thf('12', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.08  thf('13', plain,
% 0.91/1.08      (![X19 : $i, X20 : $i]:
% 0.91/1.08         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.91/1.08           = (k3_xboole_0 @ X19 @ X20))),
% 0.91/1.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.91/1.08  thf('14', plain,
% 0.91/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.08      inference('sup+', [status(thm)], ['12', '13'])).
% 0.91/1.08  thf(t3_xboole_0, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.91/1.08            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.08       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.08            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.91/1.08  thf('15', plain,
% 0.91/1.08      (![X3 : $i, X4 : $i]:
% 0.91/1.08         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.08  thf('16', plain,
% 0.91/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.08      inference('sup+', [status(thm)], ['12', '13'])).
% 0.91/1.08  thf('17', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_boole])).
% 0.91/1.08  thf('18', plain,
% 0.91/1.08      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.08      inference('sup+', [status(thm)], ['16', '17'])).
% 0.91/1.08  thf(d7_xboole_0, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.91/1.08       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.08  thf('19', plain,
% 0.91/1.08      (![X0 : $i, X2 : $i]:
% 0.91/1.08         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.08  thf('20', plain,
% 0.91/1.08      ((((k1_xboole_0) != (k1_xboole_0))
% 0.91/1.08        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['18', '19'])).
% 0.91/1.08  thf('21', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.91/1.08      inference('simplify', [status(thm)], ['20'])).
% 0.91/1.08  thf('22', plain,
% 0.91/1.08      (![X3 : $i, X4 : $i]:
% 0.91/1.08         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.08  thf('23', plain,
% 0.91/1.08      (![X3 : $i, X4 : $i]:
% 0.91/1.08         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.08  thf('24', plain,
% 0.91/1.08      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.91/1.08         (~ (r2_hidden @ X5 @ X3)
% 0.91/1.08          | ~ (r2_hidden @ X5 @ X6)
% 0.91/1.08          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.91/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.08  thf('25', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.08         ((r1_xboole_0 @ X0 @ X1)
% 0.91/1.08          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.91/1.08          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.91/1.08      inference('sup-', [status(thm)], ['23', '24'])).
% 0.91/1.08  thf('26', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((r1_xboole_0 @ X0 @ X1)
% 0.91/1.08          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.91/1.08          | (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.08      inference('sup-', [status(thm)], ['22', '25'])).
% 0.91/1.08  thf('27', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.08      inference('simplify', [status(thm)], ['26'])).
% 0.91/1.08  thf('28', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.91/1.08      inference('sup-', [status(thm)], ['21', '27'])).
% 0.91/1.08  thf('29', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.08      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.08  thf('30', plain,
% 0.91/1.08      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['28', '29'])).
% 0.91/1.08  thf(t4_xboole_0, axiom,
% 0.91/1.08    (![A:$i,B:$i]:
% 0.91/1.08     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.08            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.08       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.08            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.91/1.08  thf('31', plain,
% 0.91/1.08      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.91/1.08         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.91/1.08          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.91/1.08      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.91/1.08  thf('32', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.08  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.91/1.08      inference('sup-', [status(thm)], ['21', '27'])).
% 0.91/1.08  thf('34', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.91/1.08      inference('demod', [status(thm)], ['32', '33'])).
% 0.91/1.08  thf('35', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.91/1.08      inference('sup-', [status(thm)], ['15', '34'])).
% 0.91/1.08  thf('36', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.08      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.08  thf('37', plain,
% 0.91/1.08      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.08  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.08      inference('demod', [status(thm)], ['14', '37'])).
% 0.91/1.08  thf('39', plain,
% 0.91/1.08      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.91/1.08         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.91/1.08           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.91/1.08      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.91/1.08  thf('40', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((k1_xboole_0)
% 0.91/1.08           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.91/1.08      inference('sup+', [status(thm)], ['38', '39'])).
% 0.91/1.08  thf('41', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.91/1.08      inference('sup+', [status(thm)], ['11', '40'])).
% 0.91/1.08  thf('42', plain,
% 0.91/1.08      (![X0 : $i, X2 : $i]:
% 0.91/1.08         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.91/1.08      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.91/1.08  thf('43', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]:
% 0.91/1.08         (((k1_xboole_0) != (k1_xboole_0))
% 0.91/1.08          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.91/1.08      inference('sup-', [status(thm)], ['41', '42'])).
% 0.91/1.08  thf('44', plain,
% 0.91/1.08      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.91/1.08      inference('simplify', [status(thm)], ['43'])).
% 0.91/1.08  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.91/1.08  
% 0.91/1.08  % SZS output end Refutation
% 0.91/1.08  
% 0.91/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
