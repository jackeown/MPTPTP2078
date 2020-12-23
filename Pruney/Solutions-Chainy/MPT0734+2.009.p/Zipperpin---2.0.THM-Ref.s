%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VzrpMh9Sa3

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 ( 387 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(t22_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r1_tarski @ A @ B )
                  & ( r2_hidden @ B @ C ) )
               => ( r2_hidden @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ( ( ( r1_tarski @ A @ B )
                    & ( r2_hidden @ B @ C ) )
                 => ( r2_hidden @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('5',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_xboole_0 @ X8 @ X7 )
      | ~ ( v1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('7',plain,
    ( ( sk_A = sk_B )
    | ~ ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t19_ordinal1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_ordinal1 @ C )
     => ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ B @ C ) )
       => ( r2_hidden @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_ordinal1 @ X6 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t19_ordinal1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_A @ X0 )
      | ~ ( v1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_ordinal1 @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('16',plain,(
    v1_ordinal1 @ sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['1','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VzrpMh9Sa3
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:50:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 28 iterations in 0.013s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.47  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.47  thf(t22_ordinal1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( v3_ordinal1 @ C ) =>
% 0.21/0.47               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.21/0.47                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v1_ordinal1 @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( v3_ordinal1 @ C ) =>
% 0.21/0.47                  ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.21/0.47                    ( r2_hidden @ A @ C ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t22_ordinal1])).
% 0.21/0.47  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('2', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d8_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.47       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i]:
% 0.21/0.47         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.47  thf('5', plain, ((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(t21_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.47           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (v3_ordinal1 @ X7)
% 0.21/0.47          | (r2_hidden @ X8 @ X7)
% 0.21/0.47          | ~ (r2_xboole_0 @ X8 @ X7)
% 0.21/0.47          | ~ (v1_ordinal1 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((((sk_A) = (sk_B))
% 0.21/0.47        | ~ (v1_ordinal1 @ sk_A)
% 0.21/0.47        | (r2_hidden @ sk_A @ sk_B)
% 0.21/0.47        | ~ (v3_ordinal1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, ((v1_ordinal1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, ((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.47  thf(t19_ordinal1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( v1_ordinal1 @ C ) =>
% 0.21/0.47       ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.21/0.47         ( r2_hidden @ A @ C ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.47          | ~ (v1_ordinal1 @ X6)
% 0.21/0.47          | (r2_hidden @ X4 @ X6)
% 0.21/0.47          | ~ (r2_hidden @ X5 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t19_ordinal1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((sk_A) = (sk_B))
% 0.21/0.47          | ~ (r2_hidden @ sk_B @ X0)
% 0.21/0.47          | (r2_hidden @ sk_A @ X0)
% 0.21/0.47          | ~ (v1_ordinal1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((~ (v1_ordinal1 @ sk_C) | (r2_hidden @ sk_A @ sk_C) | ((sk_A) = (sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '12'])).
% 0.21/0.47  thf('14', plain, ((v3_ordinal1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(cc1_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.47  thf('15', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.47  thf('16', plain, ((v1_ordinal1 @ sk_C)),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain, (((r2_hidden @ sk_A @ sk_C) | ((sk_A) = (sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '16'])).
% 0.21/0.47  thf('18', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, (((sk_A) = (sk_B))),
% 0.21/0.47      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '19'])).
% 0.21/0.47  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
