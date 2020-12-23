%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jCaed5IRxV

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  58 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  210 ( 317 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(t25_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( r3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( r3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_ordinal1])).

thf('0',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_ordinal1 @ X8 )
      | ( r2_hidden @ X9 @ X8 )
      | ( X9 = X8 )
      | ( r2_hidden @ X8 @ X9 )
      | ~ ( v3_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 )
      | ( X0 = sk_A )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( r2_hidden @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( v1_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('8',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( r2_hidden @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r3_xboole_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 )
      | ( X0 = sk_A )
      | ( r3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B_1 = sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('17',plain,
    ( ( sk_B_1 = sk_A )
    | ~ ( v1_ordinal1 @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( v1_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('20',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = sk_A )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r3_xboole_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('23',plain,
    ( ( sk_B_1 = sk_A )
    | ( r3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B_1 = sk_A ),
    inference(clc,[status(thm)],['23','24'])).

thf(reflexivity_r3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( r3_xboole_0 @ A @ A ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( r3_xboole_0 @ X3 @ X3 ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_xboole_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jCaed5IRxV
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 26 iterations in 0.016s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(t25_ordinal1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.47       ( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( r3_xboole_0 @ A @ B ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.47          ( ![B:$i]: ( ( v3_ordinal1 @ B ) => ( r3_xboole_0 @ A @ B ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t25_ordinal1])).
% 0.21/0.47  thf('0', plain, (~ (r3_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t24_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.47           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.21/0.47                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X8)
% 0.21/0.47          | (r2_hidden @ X9 @ X8)
% 0.21/0.47          | ((X9) = (X8))
% 0.21/0.47          | (r2_hidden @ X8 @ X9)
% 0.21/0.47          | ~ (v3_ordinal1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X0)
% 0.21/0.47          | (r2_hidden @ sk_A @ X0)
% 0.21/0.47          | ((X0) = (sk_A))
% 0.21/0.47          | (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(d2_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_ordinal1 @ A ) <=>
% 0.21/0.47       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.47          | (r1_tarski @ X5 @ X6)
% 0.21/0.47          | ~ (v1_ordinal1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((X0) = (sk_A))
% 0.21/0.47          | (r2_hidden @ sk_A @ X0)
% 0.21/0.47          | ~ (v3_ordinal1 @ X0)
% 0.21/0.47          | ~ (v1_ordinal1 @ sk_A)
% 0.21/0.47          | (r1_tarski @ X0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(cc1_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.47  thf('7', plain, (![X4 : $i]: ((v1_ordinal1 @ X4) | ~ (v3_ordinal1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.47  thf('8', plain, ((v1_ordinal1 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((X0) = (sk_A))
% 0.21/0.47          | (r2_hidden @ sk_A @ X0)
% 0.21/0.47          | ~ (v3_ordinal1 @ X0)
% 0.21/0.47          | (r1_tarski @ X0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.47  thf(d9_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r3_xboole_0 @ A @ B ) <=>
% 0.21/0.47       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]: ((r3_xboole_0 @ X1 @ X2) | ~ (r1_tarski @ X2 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X0)
% 0.21/0.47          | (r2_hidden @ sk_A @ X0)
% 0.21/0.47          | ((X0) = (sk_A))
% 0.21/0.47          | (r3_xboole_0 @ sk_A @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain, (~ (r3_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((((sk_B_1) = (sk_A))
% 0.21/0.47        | (r2_hidden @ sk_A @ sk_B_1)
% 0.21/0.47        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ((((sk_B_1) = (sk_A)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.47          | (r1_tarski @ X5 @ X6)
% 0.21/0.47          | ~ (v1_ordinal1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((((sk_B_1) = (sk_A))
% 0.21/0.47        | ~ (v1_ordinal1 @ sk_B_1)
% 0.21/0.47        | (r1_tarski @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, (![X4 : $i]: ((v1_ordinal1 @ X4) | ~ (v3_ordinal1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.47  thf('20', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain, ((((sk_B_1) = (sk_A)) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]: ((r3_xboole_0 @ X1 @ X2) | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.21/0.47  thf('23', plain, ((((sk_B_1) = (sk_A)) | (r3_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, (~ (r3_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('25', plain, (((sk_B_1) = (sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf(reflexivity_r3_xboole_0, axiom, (![A:$i,B:$i]: ( r3_xboole_0 @ A @ A ))).
% 0.21/0.47  thf('26', plain, (![X3 : $i]: (r3_xboole_0 @ X3 @ X3)),
% 0.21/0.47      inference('cnf', [status(esa)], [reflexivity_r3_xboole_0])).
% 0.21/0.47  thf('27', plain, ($false),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '25', '26'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
