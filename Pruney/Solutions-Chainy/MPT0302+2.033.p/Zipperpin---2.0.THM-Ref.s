%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9taevml5K2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:09 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   50 (  97 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  389 ( 994 expanded)
%              Number of equality atoms :   36 ( 134 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X7 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = sk_A ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X7 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_A @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('34',plain,(
    sk_B_1 = sk_A ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9taevml5K2
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.73  % Solved by: fo/fo7.sh
% 0.53/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.73  % done 193 iterations in 0.279s
% 0.53/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.73  % SZS output start Refutation
% 0.53/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.53/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.53/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.73  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.53/0.73  thf(t2_tarski, axiom,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.53/0.73       ( ( A ) = ( B ) ) ))).
% 0.53/0.73  thf('0', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((X1) = (X0))
% 0.53/0.73          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.53/0.73          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.53/0.73      inference('cnf', [status(esa)], [t2_tarski])).
% 0.53/0.73  thf(t7_xboole_0, axiom,
% 0.53/0.73    (![A:$i]:
% 0.53/0.73     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.53/0.73          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.53/0.73  thf('1', plain,
% 0.53/0.73      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.53/0.73      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.53/0.73  thf(l54_zfmisc_1, axiom,
% 0.53/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.73     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.53/0.73       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.53/0.73  thf('2', plain,
% 0.53/0.73      (![X3 : $i, X4 : $i, X5 : $i, X7 : $i]:
% 0.53/0.73         ((r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X7))
% 0.53/0.73          | ~ (r2_hidden @ X5 @ X7)
% 0.53/0.73          | ~ (r2_hidden @ X3 @ X4))),
% 0.53/0.73      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.53/0.73  thf('3', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (((X0) = (k1_xboole_0))
% 0.53/0.73          | ~ (r2_hidden @ X2 @ X1)
% 0.53/0.73          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.53/0.73             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.73  thf('4', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.53/0.73          | ((X1) = (X0))
% 0.53/0.73          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_B @ X2)) @ 
% 0.53/0.73             (k2_zfmisc_1 @ X0 @ X2))
% 0.53/0.73          | ((X2) = (k1_xboole_0)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['0', '3'])).
% 0.53/0.73  thf(t114_zfmisc_1, conjecture,
% 0.53/0.73    (![A:$i,B:$i]:
% 0.53/0.73     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.53/0.73       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.73         ( ( A ) = ( B ) ) ) ))).
% 0.53/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.73    (~( ![A:$i,B:$i]:
% 0.53/0.73        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.53/0.73          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.73            ( ( A ) = ( B ) ) ) ) )),
% 0.53/0.73    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.53/0.73  thf('5', plain,
% 0.53/0.73      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('6', plain,
% 0.53/0.73      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.73         ((r2_hidden @ X3 @ X4)
% 0.53/0.73          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.53/0.73      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.53/0.73  thf('7', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.53/0.73          | (r2_hidden @ X1 @ sk_B_1))),
% 0.53/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.73  thf('8', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (((sk_B_1) = (k1_xboole_0))
% 0.53/0.73          | ((X0) = (sk_A))
% 0.53/0.73          | (r2_hidden @ (sk_C @ sk_A @ X0) @ X0)
% 0.53/0.73          | (r2_hidden @ (sk_C @ sk_A @ X0) @ sk_B_1))),
% 0.53/0.73      inference('sup-', [status(thm)], ['4', '7'])).
% 0.53/0.73  thf('9', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('10', plain,
% 0.53/0.73      (![X0 : $i]:
% 0.53/0.73         (((X0) = (sk_A))
% 0.53/0.73          | (r2_hidden @ (sk_C @ sk_A @ X0) @ X0)
% 0.53/0.73          | (r2_hidden @ (sk_C @ sk_A @ X0) @ sk_B_1))),
% 0.53/0.73      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.53/0.73  thf('11', plain,
% 0.53/0.73      (((r2_hidden @ (sk_C @ sk_A @ sk_B_1) @ sk_B_1) | ((sk_B_1) = (sk_A)))),
% 0.53/0.73      inference('eq_fact', [status(thm)], ['10'])).
% 0.53/0.73  thf('12', plain, (((sk_A) != (sk_B_1))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('13', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.53/0.73      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.53/0.73  thf('14', plain,
% 0.53/0.73      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.53/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.73  thf('15', plain,
% 0.53/0.73      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.53/0.73      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.53/0.73  thf('16', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.73         (((X0) = (k1_xboole_0))
% 0.53/0.73          | ~ (r2_hidden @ X2 @ X1)
% 0.53/0.73          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.53/0.73             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.73  thf('17', plain,
% 0.53/0.73      (![X0 : $i, X1 : $i]:
% 0.53/0.73         (((X0) = (k1_xboole_0))
% 0.53/0.73          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.53/0.73             (k2_zfmisc_1 @ X0 @ X1))
% 0.53/0.73          | ((X1) = (k1_xboole_0)))),
% 0.53/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.53/0.74         (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.53/0.74        | ((sk_A) = (k1_xboole_0))
% 0.53/0.74        | ((sk_B_1) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['14', '17'])).
% 0.53/0.74  thf('19', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.53/0.74        (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['18', '19', '20'])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         ((r2_hidden @ X3 @ X4)
% 0.53/0.74          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.53/0.74      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.53/0.74  thf('23', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X3 : $i, X4 : $i, X5 : $i, X7 : $i]:
% 0.53/0.74         ((r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X7))
% 0.53/0.74          | ~ (r2_hidden @ X5 @ X7)
% 0.53/0.74          | ~ (r2_hidden @ X3 @ X4))),
% 0.53/0.74      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (r2_hidden @ X1 @ X0)
% 0.53/0.74          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ sk_B_1)) @ 
% 0.53/0.74             (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      ((r2_hidden @ (k4_tarski @ (sk_C @ sk_A @ sk_B_1) @ (sk_B @ sk_B_1)) @ 
% 0.53/0.74        (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['13', '25'])).
% 0.53/0.74  thf('27', plain,
% 0.53/0.74      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      ((r2_hidden @ (k4_tarski @ (sk_C @ sk_A @ sk_B_1) @ (sk_B @ sk_B_1)) @ 
% 0.53/0.74        (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.53/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         ((r2_hidden @ X3 @ X4)
% 0.53/0.74          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.53/0.74      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.53/0.74  thf('30', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B_1) @ sk_A)),
% 0.53/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (((X1) = (X0))
% 0.53/0.74          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.53/0.74          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [t2_tarski])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      ((~ (r2_hidden @ (sk_C @ sk_A @ sk_B_1) @ sk_B_1) | ((sk_B_1) = (sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['30', '31'])).
% 0.53/0.74  thf('33', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.53/0.74  thf('34', plain, (((sk_B_1) = (sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['32', '33'])).
% 0.53/0.74  thf('35', plain, (((sk_A) != (sk_B_1))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('36', plain, ($false),
% 0.53/0.74      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
