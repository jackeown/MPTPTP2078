%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O1kNss0Jpq

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:29 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  215 ( 386 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ X27 @ ( k1_tarski @ X28 ) )
        = X27 )
      | ( r2_hidden @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['9'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X22 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r2_hidden @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['14','15'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O1kNss0Jpq
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 77 iterations in 0.040s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(t65_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.34/0.53       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (![X27 : $i, X28 : $i]:
% 0.34/0.53         (((k4_xboole_0 @ X27 @ (k1_tarski @ X28)) = (X27))
% 0.34/0.53          | (r2_hidden @ X28 @ X27))),
% 0.34/0.53      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.34/0.53  thf(t83_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (![X9 : $i, X11 : $i]:
% 0.34/0.53         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((X0) != (X0))
% 0.34/0.53          | (r2_hidden @ X1 @ X0)
% 0.34/0.53          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.34/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X2 : $i, X3 : $i]:
% 0.34/0.53         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (![X9 : $i, X10 : $i]:
% 0.34/0.53         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.34/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         ((r2_hidden @ X1 @ X0)
% 0.34/0.53          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.53  thf(t69_zfmisc_1, conjecture,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.34/0.53       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i]:
% 0.34/0.53        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.34/0.53          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.53  thf('10', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.34/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.34/0.53  thf('11', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.34/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.34/0.53  thf(t38_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.34/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.34/0.53         ((r1_tarski @ (k2_tarski @ X22 @ X24) @ X25)
% 0.34/0.53          | ~ (r2_hidden @ X24 @ X25)
% 0.34/0.53          | ~ (r2_hidden @ X22 @ X25))),
% 0.34/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X0 @ sk_B)
% 0.34/0.53          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.34/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf('14', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.34/0.53  thf(t69_enumset1, axiom,
% 0.34/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.34/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.53  thf('16', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.34/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.34/0.53  thf(l32_xboole_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (![X4 : $i, X6 : $i]:
% 0.34/0.53         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.34/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('20', plain, ($false),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
