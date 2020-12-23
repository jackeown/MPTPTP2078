%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1DaSKzGxhc

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  149 ( 221 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t67_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ B @ C ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t67_xboole_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('6',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['7','10'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1DaSKzGxhc
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:07:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 65 iterations in 0.015s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(t67_xboole_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.48         ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.48            ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.48          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t67_xboole_1])).
% 0.21/0.48  thf('0', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t37_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X5 : $i, X7 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.21/0.48  thf('2', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t48_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.21/0.48           = (k3_xboole_0 @ X9 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(t3_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.48  thf('5', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.48  thf('6', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t63_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.48       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X11 @ X12)
% 0.21/0.48          | ~ (r1_xboole_0 @ X12 @ X13)
% 0.21/0.48          | (r1_xboole_0 @ X11 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.48  thf(d7_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.48  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['6', '13'])).
% 0.21/0.48  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
