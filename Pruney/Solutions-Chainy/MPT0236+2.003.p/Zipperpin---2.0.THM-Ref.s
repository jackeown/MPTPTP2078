%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dzfroDq5l0

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:58 EST 2020

% Result     : Theorem 3.90s
% Output     : Refutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   47 (  98 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  422 ( 975 expanded)
%              Number of equality atoms :   48 ( 114 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t31_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X17: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X13 ) @ X13 )
      | ( r2_hidden @ ( sk_C @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('8',plain,(
    ! [X13: $i,X17: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X17 @ X13 ) @ X13 )
      | ( r2_hidden @ ( sk_C @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('9',plain,(
    ! [X13: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ ( sk_C @ X17 @ X13 ) @ X18 )
      | ~ ( r2_hidden @ X18 @ X13 )
      | ~ ( r2_hidden @ ( sk_C @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X0
        = ( k3_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('17',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X13: $i,X17: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ( r2_hidden @ ( sk_C @ X17 @ X13 ) @ ( sk_D_1 @ X17 @ X13 ) )
      | ( r2_hidden @ ( sk_C @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X13: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ ( sk_C @ X17 @ X13 ) @ X18 )
      | ~ ( r2_hidden @ X18 @ X13 )
      | ~ ( r2_hidden @ ( sk_C @ X17 @ X13 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dzfroDq5l0
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.90/4.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.90/4.07  % Solved by: fo/fo7.sh
% 3.90/4.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.90/4.07  % done 848 iterations in 3.602s
% 3.90/4.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.90/4.07  % SZS output start Refutation
% 3.90/4.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.90/4.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.90/4.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.90/4.07  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 3.90/4.07  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.90/4.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.90/4.07  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.90/4.07  thf(sk_A_type, type, sk_A: $i).
% 3.90/4.07  thf(t31_zfmisc_1, conjecture,
% 3.90/4.07    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 3.90/4.07  thf(zf_stmt_0, negated_conjecture,
% 3.90/4.07    (~( ![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 3.90/4.07    inference('cnf.neg', [status(esa)], [t31_zfmisc_1])).
% 3.90/4.07  thf('0', plain, (((k3_tarski @ (k1_tarski @ sk_A)) != (sk_A))),
% 3.90/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.90/4.07  thf(t70_enumset1, axiom,
% 3.90/4.07    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.90/4.07  thf('1', plain,
% 3.90/4.07      (![X9 : $i, X10 : $i]:
% 3.90/4.07         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 3.90/4.07      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.90/4.07  thf(t76_enumset1, axiom,
% 3.90/4.07    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.90/4.07  thf('2', plain,
% 3.90/4.07      (![X11 : $i]: ((k1_enumset1 @ X11 @ X11 @ X11) = (k1_tarski @ X11))),
% 3.90/4.07      inference('cnf', [status(esa)], [t76_enumset1])).
% 3.90/4.07  thf('3', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 3.90/4.07      inference('sup+', [status(thm)], ['1', '2'])).
% 3.90/4.07  thf(d2_tarski, axiom,
% 3.90/4.07    (![A:$i,B:$i,C:$i]:
% 3.90/4.07     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 3.90/4.07       ( ![D:$i]:
% 3.90/4.07         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 3.90/4.07  thf('4', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.90/4.07         (((X1) != (X0))
% 3.90/4.07          | (r2_hidden @ X1 @ X2)
% 3.90/4.07          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 3.90/4.07      inference('cnf', [status(esa)], [d2_tarski])).
% 3.90/4.07  thf('5', plain,
% 3.90/4.07      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 3.90/4.07      inference('simplify', [status(thm)], ['4'])).
% 3.90/4.07  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.90/4.07      inference('sup+', [status(thm)], ['3', '5'])).
% 3.90/4.07  thf(d4_tarski, axiom,
% 3.90/4.07    (![A:$i,B:$i]:
% 3.90/4.07     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 3.90/4.07       ( ![C:$i]:
% 3.90/4.07         ( ( r2_hidden @ C @ B ) <=>
% 3.90/4.07           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 3.90/4.07  thf('7', plain,
% 3.90/4.07      (![X13 : $i, X17 : $i]:
% 3.90/4.07         (((X17) = (k3_tarski @ X13))
% 3.90/4.07          | (r2_hidden @ (sk_D_1 @ X17 @ X13) @ X13)
% 3.90/4.07          | (r2_hidden @ (sk_C @ X17 @ X13) @ X17))),
% 3.90/4.07      inference('cnf', [status(esa)], [d4_tarski])).
% 3.90/4.07  thf('8', plain,
% 3.90/4.07      (![X13 : $i, X17 : $i]:
% 3.90/4.07         (((X17) = (k3_tarski @ X13))
% 3.90/4.07          | (r2_hidden @ (sk_D_1 @ X17 @ X13) @ X13)
% 3.90/4.07          | (r2_hidden @ (sk_C @ X17 @ X13) @ X17))),
% 3.90/4.07      inference('cnf', [status(esa)], [d4_tarski])).
% 3.90/4.07  thf('9', plain,
% 3.90/4.07      (![X13 : $i, X17 : $i, X18 : $i]:
% 3.90/4.07         (((X17) = (k3_tarski @ X13))
% 3.90/4.07          | ~ (r2_hidden @ (sk_C @ X17 @ X13) @ X18)
% 3.90/4.07          | ~ (r2_hidden @ X18 @ X13)
% 3.90/4.07          | ~ (r2_hidden @ (sk_C @ X17 @ X13) @ X17))),
% 3.90/4.07      inference('cnf', [status(esa)], [d4_tarski])).
% 3.90/4.07  thf('10', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         ((r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1)
% 3.90/4.07          | ((X0) = (k3_tarski @ X1))
% 3.90/4.07          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 3.90/4.07          | ~ (r2_hidden @ X0 @ X1)
% 3.90/4.07          | ((X0) = (k3_tarski @ X1)))),
% 3.90/4.07      inference('sup-', [status(thm)], ['8', '9'])).
% 3.90/4.07  thf('11', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         (~ (r2_hidden @ X0 @ X1)
% 3.90/4.07          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 3.90/4.07          | ((X0) = (k3_tarski @ X1))
% 3.90/4.07          | (r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1))),
% 3.90/4.07      inference('simplify', [status(thm)], ['10'])).
% 3.90/4.07  thf('12', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         ((r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1)
% 3.90/4.07          | ((X0) = (k3_tarski @ X1))
% 3.90/4.07          | (r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1)
% 3.90/4.07          | ((X0) = (k3_tarski @ X1))
% 3.90/4.07          | ~ (r2_hidden @ X0 @ X1))),
% 3.90/4.07      inference('sup-', [status(thm)], ['7', '11'])).
% 3.90/4.07  thf('13', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         (~ (r2_hidden @ X0 @ X1)
% 3.90/4.07          | ((X0) = (k3_tarski @ X1))
% 3.90/4.07          | (r2_hidden @ (sk_D_1 @ X0 @ X1) @ X1))),
% 3.90/4.07      inference('simplify', [status(thm)], ['12'])).
% 3.90/4.07  thf('14', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         ((r2_hidden @ (sk_D_1 @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0))
% 3.90/4.07          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 3.90/4.07      inference('sup-', [status(thm)], ['6', '13'])).
% 3.90/4.07  thf('15', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 3.90/4.07      inference('sup+', [status(thm)], ['1', '2'])).
% 3.90/4.07  thf('16', plain,
% 3.90/4.07      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.90/4.07         (~ (r2_hidden @ X4 @ X2)
% 3.90/4.07          | ((X4) = (X3))
% 3.90/4.07          | ((X4) = (X0))
% 3.90/4.07          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 3.90/4.07      inference('cnf', [status(esa)], [d2_tarski])).
% 3.90/4.07  thf('17', plain,
% 3.90/4.07      (![X0 : $i, X3 : $i, X4 : $i]:
% 3.90/4.07         (((X4) = (X0))
% 3.90/4.07          | ((X4) = (X3))
% 3.90/4.07          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 3.90/4.07      inference('simplify', [status(thm)], ['16'])).
% 3.90/4.07  thf('18', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 3.90/4.07      inference('sup-', [status(thm)], ['15', '17'])).
% 3.90/4.07  thf('19', plain,
% 3.90/4.07      (![X0 : $i, X1 : $i]:
% 3.90/4.07         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 3.90/4.07      inference('simplify', [status(thm)], ['18'])).
% 3.90/4.07  thf('20', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 3.90/4.07          | ((sk_D_1 @ X0 @ (k1_tarski @ X0)) = (X0)))),
% 3.90/4.07      inference('sup-', [status(thm)], ['14', '19'])).
% 3.90/4.07  thf('21', plain,
% 3.90/4.07      (![X13 : $i, X17 : $i]:
% 3.90/4.07         (((X17) = (k3_tarski @ X13))
% 3.90/4.07          | (r2_hidden @ (sk_C @ X17 @ X13) @ (sk_D_1 @ X17 @ X13))
% 3.90/4.07          | (r2_hidden @ (sk_C @ X17 @ X13) @ X17))),
% 3.90/4.07      inference('cnf', [status(esa)], [d4_tarski])).
% 3.90/4.07  thf('22', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 3.90/4.07          | ((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 3.90/4.07          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 3.90/4.07          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 3.90/4.07      inference('sup+', [status(thm)], ['20', '21'])).
% 3.90/4.07  thf('23', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 3.90/4.07          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0))),
% 3.90/4.07      inference('simplify', [status(thm)], ['22'])).
% 3.90/4.07  thf('24', plain,
% 3.90/4.07      (![X13 : $i, X17 : $i, X18 : $i]:
% 3.90/4.07         (((X17) = (k3_tarski @ X13))
% 3.90/4.07          | ~ (r2_hidden @ (sk_C @ X17 @ X13) @ X18)
% 3.90/4.07          | ~ (r2_hidden @ X18 @ X13)
% 3.90/4.07          | ~ (r2_hidden @ (sk_C @ X17 @ X13) @ X17))),
% 3.90/4.07      inference('cnf', [status(esa)], [d4_tarski])).
% 3.90/4.07  thf('25', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 3.90/4.07          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 3.90/4.07          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 3.90/4.07          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 3.90/4.07      inference('sup-', [status(thm)], ['23', '24'])).
% 3.90/4.07  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.90/4.07      inference('sup+', [status(thm)], ['3', '5'])).
% 3.90/4.07  thf('27', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 3.90/4.07          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 3.90/4.07          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 3.90/4.07      inference('demod', [status(thm)], ['25', '26'])).
% 3.90/4.07  thf('28', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         (~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0)
% 3.90/4.07          | ((X0) = (k3_tarski @ (k1_tarski @ X0))))),
% 3.90/4.07      inference('simplify', [status(thm)], ['27'])).
% 3.90/4.07  thf('29', plain,
% 3.90/4.07      (![X0 : $i]:
% 3.90/4.07         (((X0) = (k3_tarski @ (k1_tarski @ X0)))
% 3.90/4.07          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ X0)) @ X0))),
% 3.90/4.07      inference('simplify', [status(thm)], ['22'])).
% 3.90/4.07  thf('30', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 3.90/4.07      inference('clc', [status(thm)], ['28', '29'])).
% 3.90/4.07  thf('31', plain, (((sk_A) != (sk_A))),
% 3.90/4.07      inference('demod', [status(thm)], ['0', '30'])).
% 3.90/4.07  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 3.90/4.07  
% 3.90/4.07  % SZS output end Refutation
% 3.90/4.07  
% 3.90/4.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
