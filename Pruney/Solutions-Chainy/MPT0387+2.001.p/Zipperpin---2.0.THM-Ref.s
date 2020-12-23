%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VwKuouTVNL

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  246 ( 309 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('3',plain,(
    ! [X22: $i,X23: $i,X25: $i,X26: $i] :
      ( ( X22
       != ( k1_setfam_1 @ X23 ) )
      | ~ ( r2_hidden @ X25 @ X23 )
      | ( r2_hidden @ X26 @ X25 )
      | ~ ( r2_hidden @ X26 @ X22 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('4',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r2_hidden @ X26 @ ( k1_setfam_1 @ X23 ) )
      | ( r2_hidden @ X26 @ X25 )
      | ~ ( r2_hidden @ X25 @ X23 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( k1_setfam_1 @ X0 ) ) @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k1_setfam_1 @ sk_A ) ) @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ( k1_setfam_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k1_setfam_1 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['17'])).

thf('19',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X23: $i,X28: $i] :
      ( ( X28
       != ( k1_setfam_1 @ X23 ) )
      | ( X28 = k1_xboole_0 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('21',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','19','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VwKuouTVNL
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 209 iterations in 0.095s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(t5_setfam_1, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.22/0.55       ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.22/0.55          ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t5_setfam_1])).
% 0.22/0.55  thf('0', plain, (((k1_setfam_1 @ sk_A) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t7_xboole_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X12 : $i]:
% 0.22/0.55         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.55  thf(d1_setfam_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.22/0.55         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.55       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.55         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.55               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X22 : $i, X23 : $i, X25 : $i, X26 : $i]:
% 0.22/0.55         (((X22) != (k1_setfam_1 @ X23))
% 0.22/0.55          | ~ (r2_hidden @ X25 @ X23)
% 0.22/0.55          | (r2_hidden @ X26 @ X25)
% 0.22/0.55          | ~ (r2_hidden @ X26 @ X22)
% 0.22/0.55          | ((X23) = (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.22/0.55         (((X23) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X26 @ (k1_setfam_1 @ X23))
% 0.22/0.55          | (r2_hidden @ X26 @ X25)
% 0.22/0.55          | ~ (r2_hidden @ X25 @ X23))),
% 0.22/0.55      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((k1_setfam_1 @ X0) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X1 @ X0)
% 0.22/0.55          | (r2_hidden @ (sk_B @ (k1_setfam_1 @ X0)) @ X1)
% 0.22/0.55          | ((X0) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      ((((sk_A) = (k1_xboole_0))
% 0.22/0.55        | (r2_hidden @ (sk_B @ (k1_setfam_1 @ sk_A)) @ k1_xboole_0)
% 0.22/0.55        | ((k1_setfam_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '5'])).
% 0.22/0.55  thf('7', plain, (((k1_setfam_1 @ sk_A) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      ((((sk_A) = (k1_xboole_0))
% 0.22/0.55        | (r2_hidden @ (sk_B @ (k1_setfam_1 @ sk_A)) @ k1_xboole_0))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf(d3_tarski, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X3 : $i, X5 : $i]:
% 0.22/0.55         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      (![X3 : $i, X5 : $i]:
% 0.22/0.55         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.55  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.22/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.55  thf(l32_xboole_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X13 : $i, X15 : $i]:
% 0.22/0.55         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.22/0.55          | ~ (r1_tarski @ X13 @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.55  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf(d5_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.55       ( ![D:$i]:
% 0.22/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.22/0.55          | ~ (r2_hidden @ X10 @ X8)
% 0.22/0.55          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X10 @ X8)
% 0.22/0.55          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['14', '16'])).
% 0.22/0.55  thf('18', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.55      inference('condensation', [status(thm)], ['17'])).
% 0.22/0.55  thf('19', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.55      inference('clc', [status(thm)], ['8', '18'])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X23 : $i, X28 : $i]:
% 0.22/0.55         (((X28) != (k1_setfam_1 @ X23))
% 0.22/0.55          | ((X28) = (k1_xboole_0))
% 0.22/0.55          | ((X23) != (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.22/0.55  thf('21', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.55  thf('22', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['0', '19', '21'])).
% 0.22/0.55  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
