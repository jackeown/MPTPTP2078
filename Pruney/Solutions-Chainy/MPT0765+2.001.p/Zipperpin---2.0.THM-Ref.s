%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ITndA7N9vz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  71 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  319 ( 832 expanded)
%              Number of equality atoms :   19 (  46 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t10_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( r2_hidden @ D @ B )
                       => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ~ ( v2_wellord1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 )
      | ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ ( k3_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ ( k3_relat_1 @ X0 ) @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ ( k3_relat_1 @ X0 ) @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t11_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ~ ( ( v2_wellord1 @ A )
          & ( ( k3_relat_1 @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
                & ! [C: $i] :
                    ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                   => ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ~ ( ( v2_wellord1 @ A )
            & ( ( k3_relat_1 @ A )
             != k1_xboole_0 )
            & ! [B: $i] :
                ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
                  & ! [C: $i] :
                      ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                     => ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord1])).

thf('5',plain,(
    ! [X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ X6 ) @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ( k3_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( sk_C_1 @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v2_wellord1 @ X3 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X3 ) @ X4 ) @ X3 )
      | ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ ( k3_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k3_relat_1 @ X0 ) @ X0 ) @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) ) @ sk_A )
    | ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) ) @ sk_A )
    | ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ( k3_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( sk_C_1 @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_C_1 @ X6 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( r2_hidden @ ( sk_C @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v2_wellord1 @ sk_A )
    | ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k3_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ( k3_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ITndA7N9vz
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 31 iterations in 0.025s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.49  thf(t10_wellord1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( v2_wellord1 @ A ) =>
% 0.20/0.49         ( ![B:$i]:
% 0.20/0.49           ( ~( ( r1_tarski @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.49                ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49                ( ![C:$i]:
% 0.20/0.49                  ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.49                       ( ![D:$i]:
% 0.20/0.49                         ( ( r2_hidden @ D @ B ) =>
% 0.20/0.49                           ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X3 : $i, X5 : $i]:
% 0.20/0.49         (~ (v2_wellord1 @ X3)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X5 @ X3) @ X5)
% 0.20/0.49          | ((X5) = (k1_xboole_0))
% 0.20/0.49          | ~ (r1_tarski @ X5 @ (k3_relat_1 @ X3))
% 0.20/0.49          | ~ (v1_relat_1 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t10_wellord1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.20/0.49          | (r2_hidden @ (sk_C @ (k3_relat_1 @ X0) @ X0) @ (k3_relat_1 @ X0))
% 0.20/0.49          | ~ (v2_wellord1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.20/0.49          | (r2_hidden @ (sk_C @ (k3_relat_1 @ X0) @ X0) @ (k3_relat_1 @ X0))
% 0.20/0.49          | ~ (v2_wellord1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(t11_wellord1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ~( ( v2_wellord1 @ A ) & ( ( k3_relat_1 @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49            ( ![B:$i]:
% 0.20/0.49              ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.49                   ( ![C:$i]:
% 0.20/0.49                     ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) =>
% 0.20/0.49                       ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ A ) =>
% 0.20/0.49          ( ~( ( v2_wellord1 @ A ) & 
% 0.20/0.49               ( ( k3_relat_1 @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49               ( ![B:$i]:
% 0.20/0.49                 ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.49                      ( ![C:$i]:
% 0.20/0.49                        ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) =>
% 0.20/0.49                          ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t11_wellord1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X6 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X6 @ (k3_relat_1 @ sk_A))
% 0.20/0.49          | (r2_hidden @ (sk_C_1 @ X6) @ (k3_relat_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((~ (v2_wellord1 @ sk_A)
% 0.20/0.49        | ((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.49        | (r2_hidden @ (sk_C_1 @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A)) @ 
% 0.20/0.49           (k3_relat_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain, ((v2_wellord1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | (r2_hidden @ (sk_C_1 @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A)) @ 
% 0.20/0.49           (k3_relat_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.49  thf('10', plain, (((k3_relat_1 @ sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((r2_hidden @ (sk_C_1 @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A)) @ 
% 0.20/0.49        (k3_relat_1 @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (v2_wellord1 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ X5)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X3) @ X4) @ X3)
% 0.20/0.49          | ((X5) = (k1_xboole_0))
% 0.20/0.49          | ~ (r1_tarski @ X5 @ (k3_relat_1 @ X3))
% 0.20/0.49          | ~ (v1_relat_1 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t10_wellord1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_C @ (k3_relat_1 @ X0) @ X0) @ X1) @ 
% 0.20/0.49             X0)
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.20/0.49          | ~ (v2_wellord1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((~ (v2_wellord1 @ sk_A)
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k4_tarski @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.20/0.49            (sk_C_1 @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A))) @ 
% 0.20/0.49           sk_A)
% 0.20/0.49        | ((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.49  thf('16', plain, ((v2_wellord1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((r2_hidden @ 
% 0.20/0.49         (k4_tarski @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.20/0.49          (sk_C_1 @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A))) @ 
% 0.20/0.49         sk_A)
% 0.20/0.49        | ((k3_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.49  thf('19', plain, (((k3_relat_1 @ sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((r2_hidden @ 
% 0.20/0.49        (k4_tarski @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.20/0.49         (sk_C_1 @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A))) @ 
% 0.20/0.49        sk_A)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X6 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X6 @ (k3_relat_1 @ sk_A))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X6 @ (sk_C_1 @ X6)) @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (~ (r2_hidden @ (sk_C @ (k3_relat_1 @ sk_A) @ sk_A) @ (k3_relat_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((~ (v2_wellord1 @ sk_A)
% 0.20/0.49        | ((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '22'])).
% 0.20/0.49  thf('24', plain, ((v2_wellord1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain, (((k3_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.49  thf('27', plain, (((k3_relat_1 @ sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
