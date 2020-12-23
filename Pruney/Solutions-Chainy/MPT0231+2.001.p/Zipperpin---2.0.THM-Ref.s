%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P6VWL51rFS

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:28 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  296 ( 385 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50
        = ( k1_tarski @ X49 ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( r1_tarski @ ( k1_tarski @ X52 ) @ ( k2_tarski @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('4',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C_2 ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50
        = ( k1_tarski @ X49 ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('6',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X52: $i,X53: $i] :
      ( r1_tarski @ ( k1_tarski @ X52 ) @ ( k2_tarski @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['8','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X31 != X30 )
      | ( r2_hidden @ X31 @ X32 )
      | ( X32
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X30: $i] :
      ( r2_hidden @ X30 @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( X33 = X30 )
      | ( X32
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_C_2 = sk_A ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    sk_A != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X30: $i] :
      ( r2_hidden @ X30 @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('22',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['28'])).

thf('30',plain,(
    $false ),
    inference('sup-',[status(thm)],['22','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P6VWL51rFS
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:34:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 351 iterations in 0.127s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.58  thf(t26_zfmisc_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.38/0.58       ( ( A ) = ( C ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.58        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.38/0.58          ( ( A ) = ( C ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_2))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(l3_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.38/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X49 : $i, X50 : $i]:
% 0.38/0.58         (((X50) = (k1_tarski @ X49))
% 0.38/0.58          | ((X50) = (k1_xboole_0))
% 0.38/0.58          | ~ (r1_tarski @ X50 @ (k1_tarski @ X49)))),
% 0.38/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.58        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C_2)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.58  thf(t12_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X52 : $i, X53 : $i]:
% 0.38/0.58         (r1_tarski @ (k1_tarski @ X52) @ (k2_tarski @ X52 @ X53))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C_2))
% 0.38/0.58        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X49 : $i, X50 : $i]:
% 0.38/0.58         (((X50) = (k1_tarski @ X49))
% 0.38/0.58          | ((X50) = (k1_xboole_0))
% 0.38/0.58          | ~ (r1_tarski @ X50 @ (k1_tarski @ X49)))),
% 0.38/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.58        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.58        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_2)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X52 : $i, X53 : $i]:
% 0.38/0.58         (r1_tarski @ (k1_tarski @ X52) @ (k2_tarski @ X52 @ X53))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.38/0.58        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_2))
% 0.38/0.58        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.58  thf('9', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.58  thf(d10_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X10 : $i, X12 : $i]:
% 0.38/0.58         (((X10) = (X12))
% 0.38/0.58          | ~ (r1_tarski @ X12 @ X10)
% 0.38/0.58          | ~ (r1_tarski @ X10 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.38/0.58        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C_2)))),
% 0.38/0.58      inference('clc', [status(thm)], ['8', '11'])).
% 0.38/0.58  thf(d1_tarski, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.38/0.58         (((X31) != (X30))
% 0.38/0.58          | (r2_hidden @ X31 @ X32)
% 0.38/0.58          | ((X32) != (k1_tarski @ X30)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.58  thf('14', plain, (![X30 : $i]: (r2_hidden @ X30 @ (k1_tarski @ X30))),
% 0.38/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (((r2_hidden @ sk_C_2 @ (k1_tarski @ sk_A))
% 0.38/0.58        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['12', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X30 : $i, X32 : $i, X33 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X33 @ X32)
% 0.38/0.58          | ((X33) = (X30))
% 0.38/0.58          | ((X32) != (k1_tarski @ X30)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X30 : $i, X33 : $i]:
% 0.38/0.58         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_C_2) = (sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['15', '17'])).
% 0.38/0.58  thf('19', plain, (((sk_A) != (sk_C_2))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('20', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.38/0.58  thf('21', plain, (![X30 : $i]: (r2_hidden @ X30 @ (k1_tarski @ X30))),
% 0.38/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.58  thf('22', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.38/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf(t36_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.38/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.58  thf(d5_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.38/0.58       ( ![D:$i]:
% 0.38/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.58          | ~ (r2_hidden @ X4 @ X2)
% 0.38/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X4 @ X2)
% 0.38/0.58          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['25', '27'])).
% 0.38/0.58  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.58      inference('condensation', [status(thm)], ['28'])).
% 0.38/0.58  thf('30', plain, ($false), inference('sup-', [status(thm)], ['22', '29'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
