%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.20X1S1lYxj

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:30 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 116 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  461 ( 947 expanded)
%              Number of equality atoms :   51 ( 103 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15 != X14 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['11'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','35'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('41',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.20X1S1lYxj
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:03:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.69/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.91  % Solved by: fo/fo7.sh
% 0.69/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.91  % done 821 iterations in 0.471s
% 0.69/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.91  % SZS output start Refutation
% 0.69/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.69/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.91  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.91  thf(d1_tarski, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.69/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.69/0.91  thf('0', plain,
% 0.69/0.91      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.91         (((X15) != (X14))
% 0.69/0.91          | (r2_hidden @ X15 @ X16)
% 0.69/0.91          | ((X16) != (k1_tarski @ X14)))),
% 0.69/0.91      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.91  thf('1', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_tarski @ X14))),
% 0.69/0.91      inference('simplify', [status(thm)], ['0'])).
% 0.69/0.91  thf(d5_xboole_0, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.69/0.91       ( ![D:$i]:
% 0.69/0.91         ( ( r2_hidden @ D @ C ) <=>
% 0.69/0.91           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.69/0.91  thf('2', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.91          | (r2_hidden @ X0 @ X2)
% 0.69/0.91          | (r2_hidden @ X0 @ X3)
% 0.69/0.91          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.69/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.91  thf('3', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.69/0.91          | (r2_hidden @ X0 @ X2)
% 0.69/0.91          | ~ (r2_hidden @ X0 @ X1))),
% 0.69/0.91      inference('simplify', [status(thm)], ['2'])).
% 0.69/0.91  thf('4', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ X0 @ X1)
% 0.69/0.91          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['1', '3'])).
% 0.69/0.91  thf('5', plain,
% 0.69/0.91      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.69/0.91         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.69/0.91          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.69/0.91          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.69/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.91  thf(t1_boole, axiom,
% 0.69/0.91    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.91  thf('6', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.69/0.91      inference('cnf', [status(esa)], [t1_boole])).
% 0.69/0.91  thf(t46_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.69/0.91  thf('7', plain,
% 0.69/0.91      (![X10 : $i, X11 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.69/0.91      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.69/0.91  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['6', '7'])).
% 0.69/0.91  thf('9', plain,
% 0.69/0.91      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X4 @ X3)
% 0.69/0.91          | ~ (r2_hidden @ X4 @ X2)
% 0.69/0.91          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.69/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.91  thf('10', plain,
% 0.69/0.91      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X4 @ X2)
% 0.69/0.91          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.69/0.91      inference('simplify', [status(thm)], ['9'])).
% 0.69/0.91  thf('11', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['8', '10'])).
% 0.69/0.91  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.69/0.91      inference('condensation', [status(thm)], ['11'])).
% 0.69/0.91  thf('13', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.69/0.91          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['5', '12'])).
% 0.69/0.91  thf('14', plain,
% 0.69/0.91      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X17 @ X16)
% 0.69/0.91          | ((X17) = (X14))
% 0.69/0.91          | ((X16) != (k1_tarski @ X14)))),
% 0.69/0.91      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.91  thf('15', plain,
% 0.69/0.91      (![X14 : $i, X17 : $i]:
% 0.69/0.91         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.69/0.91      inference('simplify', [status(thm)], ['14'])).
% 0.69/0.91  thf('16', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.69/0.91          | ((sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['13', '15'])).
% 0.69/0.91  thf('17', plain,
% 0.69/0.91      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.69/0.91         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.69/0.91          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.69/0.91          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.69/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.91  thf('18', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.91          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.69/0.91          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 0.69/0.91             k1_xboole_0)
% 0.69/0.91          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.91  thf('19', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 0.69/0.91           k1_xboole_0)
% 0.69/0.91          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.69/0.91          | ~ (r2_hidden @ X0 @ X1))),
% 0.69/0.91      inference('simplify', [status(thm)], ['18'])).
% 0.69/0.91  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.69/0.91      inference('condensation', [status(thm)], ['11'])).
% 0.69/0.91  thf('21', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.91          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.69/0.91      inference('clc', [status(thm)], ['19', '20'])).
% 0.69/0.91  thf('22', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ X1 @ X0)
% 0.69/0.91          | ((k1_xboole_0)
% 0.69/0.91              = (k4_xboole_0 @ (k1_tarski @ X1) @ 
% 0.69/0.91                 (k4_xboole_0 @ (k1_tarski @ X1) @ X0))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['4', '21'])).
% 0.69/0.91  thf(t48_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.69/0.91  thf('23', plain,
% 0.69/0.91      (![X12 : $i, X13 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.69/0.91           = (k3_xboole_0 @ X12 @ X13))),
% 0.69/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.91  thf('24', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         ((r2_hidden @ X1 @ X0)
% 0.69/0.91          | ((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.69/0.91      inference('demod', [status(thm)], ['22', '23'])).
% 0.69/0.91  thf(t100_xboole_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.69/0.91  thf('25', plain,
% 0.69/0.91      (![X6 : $i, X7 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X6 @ X7)
% 0.69/0.91           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.69/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.91  thf('26', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 0.69/0.91            = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 0.69/0.91          | (r2_hidden @ X1 @ X0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['24', '25'])).
% 0.69/0.91  thf(t3_boole, axiom,
% 0.69/0.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.91  thf('27', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.69/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.91  thf('28', plain,
% 0.69/0.91      (![X6 : $i, X7 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X6 @ X7)
% 0.69/0.91           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.69/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.69/0.91  thf('29', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.69/0.91      inference('sup+', [status(thm)], ['27', '28'])).
% 0.69/0.91  thf('30', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.69/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.69/0.91  thf('31', plain,
% 0.69/0.91      (![X12 : $i, X13 : $i]:
% 0.69/0.91         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.69/0.91           = (k3_xboole_0 @ X12 @ X13))),
% 0.69/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.69/0.91  thf('32', plain,
% 0.69/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['30', '31'])).
% 0.69/0.91  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['6', '7'])).
% 0.69/0.91  thf('34', plain,
% 0.69/0.91      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.91      inference('demod', [status(thm)], ['32', '33'])).
% 0.69/0.91  thf('35', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.69/0.91      inference('demod', [status(thm)], ['29', '34'])).
% 0.69/0.91  thf('36', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.69/0.91          | (r2_hidden @ X1 @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['26', '35'])).
% 0.69/0.91  thf(t69_zfmisc_1, conjecture,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.69/0.91       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.91    (~( ![A:$i,B:$i]:
% 0.69/0.91        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.69/0.91          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.69/0.91    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.69/0.91  thf('37', plain,
% 0.69/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('38', plain,
% 0.69/0.91      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.69/0.91      inference('sup-', [status(thm)], ['36', '37'])).
% 0.69/0.91  thf('39', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.69/0.91      inference('simplify', [status(thm)], ['38'])).
% 0.69/0.91  thf('40', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.91          | ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.69/0.91      inference('clc', [status(thm)], ['19', '20'])).
% 0.69/0.91  thf('41', plain,
% 0.69/0.91      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.69/0.91      inference('sup-', [status(thm)], ['39', '40'])).
% 0.69/0.91  thf('42', plain,
% 0.69/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('43', plain, ($false),
% 0.69/0.91      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.69/0.91  
% 0.69/0.91  % SZS output end Refutation
% 0.69/0.91  
% 0.69/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
