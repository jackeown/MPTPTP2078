%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CkbkmLifCk

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 268 expanded)
%              Number of leaves         :   15 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  259 (2302 expanded)
%              Number of equality atoms :   15 (  53 expanded)
%              Maximal formula depth    :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

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

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( v1_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('2',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('4',plain,
    ( ~ ( v1_ordinal1 @ sk_C )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v3_ordinal1 @ sk_C )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('9',plain,
    ( ( sk_B_1 = sk_C )
    | ( r2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r2_xboole_0 @ X6 @ X7 )
      | ( r2_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_1 = sk_C )
    | ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_xboole_0 @ X13 @ X12 )
      | ~ ( v1_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('15',plain,
    ( ( sk_B_1 = sk_C )
    | ~ ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_C )
    | ~ ( v3_ordinal1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B_1 = sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_B_1 = sk_C ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('24',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_xboole_0 @ X13 @ X12 )
      | ~ ( v1_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('26',plain,
    ( ( sk_A = sk_B_1 )
    | ~ ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','20'])).

thf('31',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['21','31'])).

thf('33',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_B_1 = sk_C ),
    inference(clc,[status(thm)],['18','19'])).

thf('35',plain,(
    r2_hidden @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('37',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('38',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['32','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CkbkmLifCk
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 42 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.20/0.47  thf(t22_ordinal1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_ordinal1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( v3_ordinal1 @ C ) =>
% 0.20/0.47               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.20/0.47                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( v1_ordinal1 @ A ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.47              ( ![C:$i]:
% 0.20/0.47                ( ( v3_ordinal1 @ C ) =>
% 0.20/0.47                  ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.20/0.47                    ( r2_hidden @ A @ C ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t22_ordinal1])).
% 0.20/0.47  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc1_ordinal1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.20/0.47  thf('1', plain, (![X8 : $i]: ((v1_ordinal1 @ X8) | ~ (v3_ordinal1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.20/0.47  thf('2', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d2_ordinal1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_ordinal1 @ A ) <=>
% 0.20/0.47       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.47          | (r1_tarski @ X9 @ X10)
% 0.20/0.47          | ~ (v1_ordinal1 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.20/0.47  thf('4', plain, ((~ (v1_ordinal1 @ sk_C) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, ((~ (v3_ordinal1 @ sk_C) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.47  thf('6', plain, ((v3_ordinal1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf(d8_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.47       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X2 : $i, X4 : $i]:
% 0.20/0.47         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.47  thf('9', plain, ((((sk_B_1) = (sk_C)) | (r2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t59_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.20/0.47       ( r2_xboole_0 @ A @ C ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X5 @ X6)
% 0.20/0.47          | ~ (r2_xboole_0 @ X6 @ X7)
% 0.20/0.47          | (r2_xboole_0 @ X5 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t59_xboole_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]: ((r2_xboole_0 @ sk_A @ X0) | ~ (r2_xboole_0 @ sk_B_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, ((((sk_B_1) = (sk_C)) | (r2_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.47  thf(t21_ordinal1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_ordinal1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.47           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         (~ (v3_ordinal1 @ X12)
% 0.20/0.47          | (r2_hidden @ X13 @ X12)
% 0.20/0.47          | ~ (r2_xboole_0 @ X13 @ X12)
% 0.20/0.47          | ~ (v1_ordinal1 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((((sk_B_1) = (sk_C))
% 0.20/0.47        | ~ (v1_ordinal1 @ sk_A)
% 0.20/0.47        | (r2_hidden @ sk_A @ sk_C)
% 0.20/0.47        | ~ (v3_ordinal1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, ((v1_ordinal1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((v3_ordinal1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((((sk_B_1) = (sk_C)) | (r2_hidden @ sk_A @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.47  thf('19', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain, (((sk_B_1) = (sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '20'])).
% 0.20/0.47  thf('22', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X2 : $i, X4 : $i]:
% 0.20/0.47         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.47  thf('24', plain, ((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         (~ (v3_ordinal1 @ X12)
% 0.20/0.47          | (r2_hidden @ X13 @ X12)
% 0.20/0.47          | ~ (r2_xboole_0 @ X13 @ X12)
% 0.20/0.47          | ~ (v1_ordinal1 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      ((((sk_A) = (sk_B_1))
% 0.20/0.47        | ~ (v1_ordinal1 @ sk_A)
% 0.20/0.47        | (r2_hidden @ sk_A @ sk_B_1)
% 0.20/0.47        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf('27', plain, ((v1_ordinal1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('28', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain, ((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.47  thf('30', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '20'])).
% 0.20/0.47  thf('31', plain, (((sk_A) = (sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '31'])).
% 0.20/0.47  thf('33', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain, (((sk_B_1) = (sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('35', plain, ((r2_hidden @ sk_B_1 @ sk_B_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain, (((sk_A) = (sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('37', plain, (((sk_A) = (sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('38', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.47  thf('39', plain, ($false), inference('demod', [status(thm)], ['32', '38'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.33/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
