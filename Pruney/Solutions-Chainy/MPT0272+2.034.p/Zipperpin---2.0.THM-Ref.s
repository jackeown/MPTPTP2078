%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pUeugduuC7

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:30 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :  235 ( 274 expanded)
%              Number of equality atoms :   36 (  43 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X19 ) @ X19 )
      | ( X19
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ X2 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( ( sk_C_1 @ X20 @ X19 )
       != X20 )
      | ( X19
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X2 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X2 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

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

thf('10',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pUeugduuC7
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:36:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 167 iterations in 0.112s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.41/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.58  thf(l44_zfmisc_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.41/0.58          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      (![X19 : $i, X20 : $i]:
% 0.41/0.58         (((X19) = (k1_xboole_0))
% 0.41/0.58          | (r2_hidden @ (sk_C_1 @ X20 @ X19) @ X19)
% 0.41/0.58          | ((X19) = (k1_tarski @ X20)))),
% 0.41/0.58      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.41/0.58  thf(d5_xboole_0, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.41/0.58       ( ![D:$i]:
% 0.41/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.41/0.58          | (r2_hidden @ X4 @ X1)
% 0.41/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.41/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['1'])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         (((k4_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 0.41/0.58          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.41/0.58          | (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['0', '2'])).
% 0.41/0.58  thf(d1_tarski, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.41/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X11 @ X10)
% 0.41/0.58          | ((X11) = (X8))
% 0.41/0.58          | ((X10) != (k1_tarski @ X8)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (![X8 : $i, X11 : $i]:
% 0.41/0.58         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['4'])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.41/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X2))
% 0.41/0.58          | ((sk_C_1 @ X2 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)) = (X0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['3', '5'])).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      (![X19 : $i, X20 : $i]:
% 0.41/0.58         (((X19) = (k1_xboole_0))
% 0.41/0.58          | ((sk_C_1 @ X20 @ X19) != (X20))
% 0.41/0.58          | ((X19) = (k1_tarski @ X20)))),
% 0.41/0.58      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         (((X0) != (X1))
% 0.41/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 0.41/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 0.41/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 0.41/0.58          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      (![X1 : $i, X2 : $i]:
% 0.41/0.58         (((k4_xboole_0 @ (k1_tarski @ X1) @ X2) = (k1_xboole_0))
% 0.41/0.58          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X2) = (k1_tarski @ X1)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['8'])).
% 0.41/0.58  thf(t69_zfmisc_1, conjecture,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.41/0.58       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i]:
% 0.41/0.58        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.41/0.58          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('11', plain,
% 0.41/0.58      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.41/0.58        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.41/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('14', plain, ($false),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
