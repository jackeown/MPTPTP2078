%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Azm4TzXsLM

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  227 ( 291 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t5_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ A )
     => ( ( k1_setfam_1 @ A )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k1_setfam_1 @ A )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t5_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ( X9
        = ( k1_setfam_1 @ X10 ) )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_setfam_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('5',plain,(
    ( k1_setfam_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( r1_xboole_0 @ X7 @ X7 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('10',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X10: $i,X15: $i] :
      ( ( X15
       != ( k1_setfam_1 @ X10 ) )
      | ( X15 = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('20',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','18','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Azm4TzXsLM
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:17:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 47 iterations in 0.033s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.47  thf(t5_setfam_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.19/0.47       ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.19/0.47          ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t5_setfam_1])).
% 0.19/0.47  thf('0', plain, (((k1_setfam_1 @ sk_A) != (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d1_setfam_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.19/0.47         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.47       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.19/0.47         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.47               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 0.19/0.47          | (r2_hidden @ (sk_C_1 @ X9 @ X10) @ X11)
% 0.19/0.47          | ~ (r2_hidden @ X11 @ X10)
% 0.19/0.47          | ((X9) = (k1_setfam_1 @ X10))
% 0.19/0.47          | ((X10) = (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((sk_A) = (k1_xboole_0))
% 0.19/0.47          | ((X0) = (k1_setfam_1 @ sk_A))
% 0.19/0.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ k1_xboole_0)
% 0.19/0.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_A) @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 0.19/0.47        | ((k1_xboole_0) = (k1_setfam_1 @ sk_A))
% 0.19/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('eq_fact', [status(thm)], ['3'])).
% 0.19/0.47  thf('5', plain, (((k1_setfam_1 @ sk_A) != (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 0.19/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf(d1_xboole_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.47  thf('8', plain, ((((sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf(t66_xboole_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.19/0.47       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X7 : $i]: ((r1_xboole_0 @ X7 @ X7) | ((X7) != (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.47  thf('10', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.47  thf(t3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X5 @ X3)
% 0.19/0.47          | ~ (r2_hidden @ X5 @ X6)
% 0.19/0.47          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.19/0.47          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '14'])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.47  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['10', '16'])).
% 0.19/0.47  thf('18', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['8', '17'])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X10 : $i, X15 : $i]:
% 0.19/0.47         (((X15) != (k1_setfam_1 @ X10))
% 0.19/0.47          | ((X15) = (k1_xboole_0))
% 0.19/0.47          | ((X10) != (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.19/0.47  thf('20', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.47  thf('21', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.47      inference('demod', [status(thm)], ['0', '18', '20'])).
% 0.19/0.47  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
