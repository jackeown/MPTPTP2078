%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wjXA82OSyB

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  196 ( 406 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('2',plain,(
    ~ ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('4',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('6',plain,
    ( ~ ( v1_ordinal1 @ sk_C )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v3_ordinal1 @ sk_C )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['9','12'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('15',plain,
    ( ( sk_A = sk_C )
    | ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_xboole_0 @ X11 @ X10 )
      | ~ ( v1_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('17',plain,
    ( ( sk_A = sk_C )
    | ~ ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_C )
    | ~ ( v3_ordinal1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['2','22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wjXA82OSyB
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 35 iterations in 0.019s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.50  thf(t22_ordinal1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( v3_ordinal1 @ C ) =>
% 0.21/0.50               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.21/0.50                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( v1_ordinal1 @ A ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( v3_ordinal1 @ C ) =>
% 0.21/0.50                  ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.21/0.50                    ( r2_hidden @ A @ C ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t22_ordinal1])).
% 0.21/0.50  thf('0', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t7_ordinal1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.50  thf('2', plain, (~ (r1_tarski @ sk_C @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(cc1_ordinal1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.50  thf('3', plain, (![X6 : $i]: ((v1_ordinal1 @ X6) | ~ (v3_ordinal1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.50  thf('4', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d2_ordinal1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_ordinal1 @ A ) <=>
% 0.21/0.50       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.50          | (r1_tarski @ X7 @ X8)
% 0.21/0.50          | ~ (v1_ordinal1 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.21/0.50  thf('6', plain, ((~ (v1_ordinal1 @ sk_C) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, ((~ (v3_ordinal1 @ sk_C) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.50  thf('8', plain, ((v3_ordinal1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t1_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.50       ( r1_tarski @ A @ C ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.50          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.50          | (r1_tarski @ X3 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.50  thf(d8_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.50       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.50  thf('15', plain, ((((sk_A) = (sk_C)) | (r2_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf(t21_ordinal1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.50           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (v3_ordinal1 @ X10)
% 0.21/0.50          | (r2_hidden @ X11 @ X10)
% 0.21/0.50          | ~ (r2_xboole_0 @ X11 @ X10)
% 0.21/0.50          | ~ (v1_ordinal1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((((sk_A) = (sk_C))
% 0.21/0.50        | ~ (v1_ordinal1 @ sk_A)
% 0.21/0.50        | (r2_hidden @ sk_A @ sk_C)
% 0.21/0.50        | ~ (v3_ordinal1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain, ((v1_ordinal1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain, ((v3_ordinal1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain, ((((sk_A) = (sk_C)) | (r2_hidden @ sk_A @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.50  thf('21', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain, (((sk_A) = (sk_C))),
% 0.21/0.50      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain, ($false),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '22', '23'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
