%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AYsgdAX7bV

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:22 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :  244 ( 340 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t52_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
          = ( k1_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AYsgdAX7bV
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 127 iterations in 0.088s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.54  thf(t52_zfmisc_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r2_hidden @ A @ B ) =>
% 0.36/0.54       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i]:
% 0.36/0.54        ( ( r2_hidden @ A @ B ) =>
% 0.36/0.54          ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t52_zfmisc_1])).
% 0.36/0.54  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d4_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.36/0.54       ( ![D:$i]:
% 0.36/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.54           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.36/0.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.36/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.36/0.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.36/0.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.54      inference('eq_fact', [status(thm)], ['1'])).
% 0.36/0.54  thf(d1_tarski, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X11 @ X10)
% 0.36/0.54          | ((X11) = (X8))
% 0.36/0.54          | ((X10) != (k1_tarski @ X8)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X8 : $i, X11 : $i]:
% 0.36/0.54         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['3'])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.36/0.54          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['2', '4'])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.36/0.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.54      inference('eq_fact', [status(thm)], ['1'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.36/0.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.36/0.54          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.36/0.54          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.36/0.54          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.36/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.36/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.36/0.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.36/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.36/0.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.36/0.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.54      inference('eq_fact', [status(thm)], ['1'])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.36/0.54          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.36/0.54      inference('clc', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.54          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.36/0.54          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['5', '11'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.36/0.54      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '13'])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('16', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
