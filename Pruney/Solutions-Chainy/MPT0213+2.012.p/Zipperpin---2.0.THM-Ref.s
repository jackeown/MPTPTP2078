%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lZQeGwcxSg

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  165 ( 194 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('2',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k5_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k5_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('12',plain,(
    ! [X2: $i] :
      ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','12'])).

thf(t2_zfmisc_1,conjecture,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t2_zfmisc_1])).

thf('14',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lZQeGwcxSg
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 12 iterations in 0.015s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(t7_xboole_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.47  thf(d4_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]:
% 0.20/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.47           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X11 @ X10)
% 0.20/0.47          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 0.20/0.47          | ((X10) != (k3_tarski @ X8)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_tarski])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X8 : $i, X11 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 0.20/0.47          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k3_tarski @ X0) = (k1_xboole_0))
% 0.20/0.47          | (r2_hidden @ (sk_D_1 @ (sk_B @ (k3_tarski @ X0)) @ X0) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '2'])).
% 0.20/0.47  thf(l97_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         (r1_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k5_xboole_0 @ X5 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.47  thf(t4_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.47          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.20/0.47           = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.47          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 0.20/0.47          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         (r1_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k5_xboole_0 @ X5 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.20/0.47  thf('12', plain, (![X2 : $i]: ~ (r2_hidden @ X2 @ k1_xboole_0)),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '12'])).
% 0.20/0.47  thf(t2_zfmisc_1, conjecture, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (( k3_tarski @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.47  thf('14', plain, (((k3_tarski @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
