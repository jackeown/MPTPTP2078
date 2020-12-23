%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.btMWg4dOHk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 194 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t68_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ~ ( ( r1_tarski @ C @ A )
            & ( r1_tarski @ C @ B )
            & ( r1_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_xboole_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['1','4'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('13',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.btMWg4dOHk
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 21 iterations in 0.009s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(t68_xboole_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.45       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.45            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.45        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.45          ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.45               ( r1_xboole_0 @ A @ B ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t68_xboole_1])).
% 0.20/0.45  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('2', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t63_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.45       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.45         (~ (r1_tarski @ X2 @ X3)
% 0.20/0.45          | ~ (r1_xboole_0 @ X3 @ X4)
% 0.20/0.45          | (r1_xboole_0 @ X2 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X0 : $i]: ((r1_xboole_0 @ sk_C @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('5', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.45  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.45  thf('7', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.20/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.45  thf('8', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.45         (~ (r1_tarski @ X2 @ X3)
% 0.20/0.45          | ~ (r1_xboole_0 @ X3 @ X4)
% 0.20/0.45          | (r1_xboole_0 @ X2 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X0 : $i]: ((r1_xboole_0 @ sk_C @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain, ((r1_xboole_0 @ sk_C @ sk_C)),
% 0.20/0.45      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.45  thf(t66_xboole_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.45       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.45  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.45  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.45  thf('15', plain, ($false),
% 0.20/0.45      inference('demod', [status(thm)], ['0', '13', '14'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
