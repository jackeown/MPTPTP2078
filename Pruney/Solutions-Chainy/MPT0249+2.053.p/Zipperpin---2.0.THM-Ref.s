%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3FoXkDotbw

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:45 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   44 (  87 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  260 ( 709 expanded)
%              Number of equality atoms :   34 ( 124 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ ( k1_tarski @ X21 ) )
      | ( X20
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,(
    ! [X21: $i] :
      ( r1_tarski @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
        = ( k1_tarski @ X19 ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
        = ( k1_tarski @ X19 ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_C_1 = sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3FoXkDotbw
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 209 iterations in 0.132s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.58  thf(t44_zfmisc_1, conjecture,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.58          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.58          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.58        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.58             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.58             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.37/0.58  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(l3_zfmisc_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.37/0.58       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X20 : $i, X21 : $i]:
% 0.37/0.58         ((r1_tarski @ X20 @ (k1_tarski @ X21)) | ((X20) != (k1_tarski @ X21)))),
% 0.37/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X21 : $i]: (r1_tarski @ (k1_tarski @ X21) @ (k1_tarski @ X21))),
% 0.37/0.58      inference('simplify', [status(thm)], ['1'])).
% 0.37/0.58  thf('3', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t11_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.58         ((r1_tarski @ X10 @ X11)
% 0.37/0.58          | ~ (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0) | (r1_tarski @ sk_B @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.58  thf('6', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['2', '5'])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X19 : $i, X20 : $i]:
% 0.37/0.58         (((X20) = (k1_tarski @ X19))
% 0.37/0.58          | ((X20) = (k1_xboole_0))
% 0.37/0.58          | ~ (r1_tarski @ X20 @ (k1_tarski @ X19)))),
% 0.37/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.37/0.58  thf('8', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.58  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('10', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('11', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '10'])).
% 0.37/0.58  thf(d3_tarski, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X1 : $i, X3 : $i]:
% 0.37/0.58         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.58  thf(d3_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.58       ( ![D:$i]:
% 0.37/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.58           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X4 @ X5)
% 0.37/0.58          | (r2_hidden @ X4 @ X6)
% 0.37/0.58          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.37/0.58         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.37/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         ((r1_tarski @ X0 @ X1)
% 0.37/0.58          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['12', '14'])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (![X1 : $i, X3 : $i]:
% 0.37/0.58         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.37/0.58          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.58  thf('19', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.37/0.58      inference('sup+', [status(thm)], ['11', '18'])).
% 0.37/0.58  thf('20', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X19 : $i, X20 : $i]:
% 0.37/0.58         (((X20) = (k1_tarski @ X19))
% 0.37/0.58          | ((X20) = (k1_xboole_0))
% 0.37/0.58          | ~ (r1_tarski @ X20 @ (k1_tarski @ X19)))),
% 0.37/0.58      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.58          | ((X0) = (k1_xboole_0))
% 0.37/0.58          | ((X0) = (k1_tarski @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.58  thf('23', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 0.37/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.58  thf('25', plain, ((((sk_C_1) = (sk_B)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['19', '24'])).
% 0.37/0.58  thf('26', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('27', plain, (((sk_B) != (sk_C_1))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('28', plain, ($false),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['25', '26', '27'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
