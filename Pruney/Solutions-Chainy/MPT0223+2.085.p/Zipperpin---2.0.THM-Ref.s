%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7HIY3NMko1

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  176 ( 218 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X8: $i,X11: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X11 @ X8 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( X12 = X11 )
      | ( X12 = X8 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('11',plain,(
    ! [X8: $i,X11: $i,X12: $i] :
      ( ( X12 = X8 )
      | ( X12 = X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7HIY3NMko1
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:10:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 107 iterations in 0.060s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.51  thf(t69_enumset1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.51  thf('0', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.51  thf(d2_tarski, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.51       ( ![D:$i]:
% 0.19/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.51         (((X9) != (X8))
% 0.19/0.51          | (r2_hidden @ X9 @ X10)
% 0.19/0.51          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X8 : $i, X11 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X11 @ X8))),
% 0.19/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.51  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['0', '2'])).
% 0.19/0.51  thf(t18_zfmisc_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.51         ( k1_tarski @ A ) ) =>
% 0.19/0.51       ( ( A ) = ( B ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i]:
% 0.19/0.51        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.51            ( k1_tarski @ A ) ) =>
% 0.19/0.51          ( ( A ) = ( B ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.51         = (k1_tarski @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(d4_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.19/0.51       ( ![D:$i]:
% 0.19/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.51           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.51          | (r2_hidden @ X4 @ X2)
% 0.19/0.51          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.51         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.19/0.51          | (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['4', '6'])).
% 0.19/0.51  thf('8', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['3', '7'])).
% 0.19/0.51  thf('9', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X12 @ X10)
% 0.19/0.51          | ((X12) = (X11))
% 0.19/0.51          | ((X12) = (X8))
% 0.19/0.51          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X8 : $i, X11 : $i, X12 : $i]:
% 0.19/0.51         (((X12) = (X8))
% 0.19/0.51          | ((X12) = (X11))
% 0.19/0.51          | ~ (r2_hidden @ X12 @ (k2_tarski @ X11 @ X8)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['9', '11'])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.51  thf('14', plain, (((sk_A) = (sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '13'])).
% 0.19/0.51  thf('15', plain, (((sk_A) != (sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('16', plain, ($false),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
