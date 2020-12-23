%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ebw5eup30o

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:42 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 199 expanded)
%              Number of leaves         :   15 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  317 (1933 expanded)
%              Number of equality atoms :   29 ( 161 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X22: $i] :
      ( ( X22
        = ( k3_tarski @ X18 ) )
      | ( r2_hidden @ ( sk_D_2 @ X22 @ X18 ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X22 @ X18 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('12',plain,(
    ! [X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('28',plain,
    ( k1_xboole_0
    = ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t2_zfmisc_1,conjecture,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t2_zfmisc_1])).

thf('29',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ebw5eup30o
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:45:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 74 iterations in 0.104s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.37/0.57  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.57  thf(d4_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.37/0.57       ( ![C:$i]:
% 0.37/0.57         ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.57           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      (![X18 : $i, X22 : $i]:
% 0.37/0.57         (((X22) = (k3_tarski @ X18))
% 0.37/0.57          | (r2_hidden @ (sk_D_2 @ X22 @ X18) @ X18)
% 0.37/0.57          | (r2_hidden @ (sk_C @ X22 @ X18) @ X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [d4_tarski])).
% 0.37/0.57  thf(t1_boole, axiom,
% 0.37/0.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.57  thf('1', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.57  thf(d5_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.57       ( ![D:$i]:
% 0.37/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.37/0.57         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.37/0.57          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.37/0.57          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 0.37/0.57          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.37/0.57      inference('eq_fact', [status(thm)], ['2'])).
% 0.37/0.57  thf(d3_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.57       ( ![D:$i]:
% 0.37/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.57           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.57          | (r2_hidden @ X0 @ X2)
% 0.37/0.57          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.37/0.57         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.37/0.57          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0) @ X0)
% 0.37/0.57          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['1', '6'])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X10 @ X9)
% 0.37/0.57          | ~ (r2_hidden @ X10 @ X8)
% 0.37/0.57          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X10 @ X8)
% 0.37/0.57          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X0 : $i, X2 : $i]:
% 0.37/0.57         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))
% 0.37/0.57          | ~ (r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X2 @ k1_xboole_0) @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '9'])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_D_1 @ k1_xboole_0 @ X1 @ k1_xboole_0) @ X0)
% 0.37/0.57          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['1', '6'])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X2 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))),
% 0.37/0.57      inference('clc', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf(t48_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.37/0.57           = (k3_xboole_0 @ X13 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.37/0.57           = (k3_xboole_0 @ X13 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.57           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.37/0.57           = (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['12', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X2 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))),
% 0.37/0.57      inference('clc', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.37/0.57           = (k3_xboole_0 @ X13 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X10 @ X8)
% 0.37/0.57          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.37/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.57          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.37/0.57          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['18', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X2 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))),
% 0.37/0.57      inference('clc', [status(thm)], ['10', '11'])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('25', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r2_hidden @ (sk_D_2 @ k1_xboole_0 @ X0) @ X0)
% 0.37/0.57          | ((k1_xboole_0) = (k3_tarski @ X0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '25'])).
% 0.37/0.57  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.57      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.57  thf('28', plain, (((k1_xboole_0) = (k3_tarski @ k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.57  thf(t2_zfmisc_1, conjecture, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (( k3_tarski @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t2_zfmisc_1])).
% 0.37/0.57  thf('29', plain, (((k3_tarski @ k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('30', plain, ($false),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
