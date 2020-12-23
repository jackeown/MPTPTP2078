%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wbqadp2D7o

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  168 ( 168 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('4',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X7 @ X9 )
      | ( ( k4_xboole_0 @ X7 @ X9 )
       != X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['7','15'])).

thf('17',plain,(
    $false ),
    inference('sup-',[status(thm)],['1','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wbqadp2D7o
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 38 iterations in 0.017s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(d1_tarski, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.45         (((X11) != (X10))
% 0.20/0.45          | (r2_hidden @ X11 @ X12)
% 0.20/0.45          | ((X12) != (k1_tarski @ X10)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.45  thf('1', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 0.20/0.45      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.45  thf(t49_zfmisc_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t15_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.45       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X2 : $i, X3 : $i]:
% 0.20/0.45         (((X2) = (k1_xboole_0)) | ((k2_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('5', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.45  thf(l24_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X18 : $i, X19 : $i]:
% 0.20/0.45         (~ (r1_xboole_0 @ (k1_tarski @ X18) @ X19) | ~ (r2_hidden @ X18 @ X19))),
% 0.20/0.45      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.45  thf(t46_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X5 : $i, X6 : $i]:
% 0.20/0.45         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.45  thf(t83_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X7 : $i, X9 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ X7 @ X9) | ((k4_xboole_0 @ X7 @ X9) != (X7)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k1_xboole_0) != (X0))
% 0.20/0.45          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X1 : $i]:
% 0.20/0.45         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.20/0.45      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.45  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.45  thf(t1_boole, axiom,
% 0.20/0.45    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.45  thf('13', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.45  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('15', plain, (![X1 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X1)),
% 0.20/0.45      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.45  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.20/0.45      inference('demod', [status(thm)], ['7', '15'])).
% 0.20/0.45  thf('17', plain, ($false), inference('sup-', [status(thm)], ['1', '16'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
