%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AHQwnLPRKr

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  231 ( 287 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X12 )
      | ( r2_hidden @ X13 @ X14 )
      | ( X14
       != ( k2_tarski @ X15 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X12: $i,X15: $i] :
      ( r2_hidden @ X12 @ ( k2_tarski @ X15 @ X12 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t23_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X19 @ X20 ) @ ( k1_tarski @ X20 ) )
        = ( k1_tarski @ X19 ) )
      | ( X19 = X20 ) ) ),
    inference(cnf,[status(esa)],[t23_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    | ( sk_B = sk_A ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_tarski @ sk_B )
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AHQwnLPRKr
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 145 iterations in 0.069s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(t69_enumset1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.53  thf('0', plain, (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf(d2_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (((X13) != (X12))
% 0.21/0.53          | (r2_hidden @ X13 @ X14)
% 0.21/0.53          | ((X14) != (k2_tarski @ X15 @ X12)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X12 : $i, X15 : $i]: (r2_hidden @ X12 @ (k2_tarski @ X15 @ X12))),
% 0.21/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.53  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['0', '2'])).
% 0.21/0.53  thf(commutativity_k2_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.53  thf(t23_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) != ( B ) ) =>
% 0.21/0.53       ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 0.21/0.53         ( k1_tarski @ A ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ (k2_tarski @ X19 @ X20) @ (k1_tarski @ X20))
% 0.21/0.53            = (k1_tarski @ X19))
% 0.21/0.53          | ((X19) = (X20)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t23_zfmisc_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.21/0.53            = (k1_tarski @ X0))
% 0.21/0.53          | ((X0) = (X1)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf(t59_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.21/0.53          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.21/0.53             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t47_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.21/0.53           = (k4_xboole_0 @ X6 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_A))
% 0.21/0.53         = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((((k1_tarski @ sk_B) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.21/0.53        | ((sk_B) = (sk_A)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['6', '9'])).
% 0.21/0.53  thf('11', plain, (((sk_A) != (sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (((k1_tarski @ sk_B) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf(d5_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.53          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.53          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.53  thf('16', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '15'])).
% 0.21/0.53  thf('17', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('18', plain, ($false), inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
