%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rmnMD9p8SU

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:46 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 241 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r1_xboole_0 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rmnMD9p8SU
% 0.14/0.37  % Computer   : n004.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:40:09 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.24/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 61 iterations in 0.026s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.51  thf(t68_xboole_1, conjecture,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.24/0.51       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.24/0.51            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.51        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.24/0.51          ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.24/0.51               ( r1_xboole_0 @ A @ B ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t68_xboole_1])).
% 0.24/0.51  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t7_xboole_0, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.24/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.24/0.51  thf('2', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(l32_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X7 : $i, X9 : $i]:
% 0.24/0.51         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.24/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.24/0.51  thf('4', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.51  thf(t48_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X11 : $i, X12 : $i]:
% 0.24/0.51         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.24/0.51           = (k3_xboole_0 @ X11 @ X12))),
% 0.24/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.24/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.24/0.51  thf(t3_boole, axiom,
% 0.24/0.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.51  thf('7', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.51  thf('8', plain, (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.24/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.51  thf(t4_xboole_0, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.24/0.51          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.24/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X0 @ sk_C_1) | ~ (r1_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.51  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('12', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t63_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.24/0.51       ( r1_xboole_0 @ A @ C ) ))).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.51         (~ (r1_tarski @ X13 @ X14)
% 0.24/0.51          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.24/0.51          | (r1_xboole_0 @ X13 @ X15))),
% 0.24/0.51      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (![X0 : $i]: ((r1_xboole_0 @ sk_C_1 @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.51  thf('15', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.24/0.51      inference('sup-', [status(thm)], ['11', '14'])).
% 0.24/0.51  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.24/0.51      inference('demod', [status(thm)], ['10', '15'])).
% 0.24/0.51  thf('17', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['1', '16'])).
% 0.24/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.51  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.51  thf('19', plain, ($false),
% 0.24/0.51      inference('demod', [status(thm)], ['0', '17', '18'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
