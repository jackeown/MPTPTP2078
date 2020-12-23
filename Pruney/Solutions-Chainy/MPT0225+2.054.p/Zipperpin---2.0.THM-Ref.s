%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DmuZYVU6eF

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:51 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   37 (  81 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  308 ( 797 expanded)
%              Number of equality atoms :   51 ( 135 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) )
      | ( X11 = X12 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('3',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k4_xboole_0 @ X0 @ X2 )
       != X0 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X10 ) )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('16',plain,(
    ! [X10: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','17','18'])).

thf('20',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['6','17'])).

thf('25',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DmuZYVU6eF
% 0.16/0.38  % Computer   : n024.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 15:14:06 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.24/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.48  % Solved by: fo/fo7.sh
% 0.24/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.48  % done 35 iterations in 0.016s
% 0.24/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.48  % SZS output start Refutation
% 0.24/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.48  thf(t17_zfmisc_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( ( A ) != ( B ) ) =>
% 0.24/0.48       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.24/0.48  thf('0', plain,
% 0.24/0.48      (![X11 : $i, X12 : $i]:
% 0.24/0.48         ((r1_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X12))
% 0.24/0.48          | ((X11) = (X12)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.24/0.48  thf(t83_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.48  thf('1', plain,
% 0.24/0.48      (![X0 : $i, X1 : $i]:
% 0.24/0.48         (((k4_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.24/0.48  thf('2', plain,
% 0.24/0.48      (![X0 : $i, X1 : $i]:
% 0.24/0.48         (((X1) = (X0))
% 0.24/0.48          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.24/0.48              = (k1_tarski @ X1)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.48  thf(t20_zfmisc_1, conjecture,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.24/0.48         ( k1_tarski @ A ) ) <=>
% 0.24/0.48       ( ( A ) != ( B ) ) ))).
% 0.24/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.48    (~( ![A:$i,B:$i]:
% 0.24/0.48        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.24/0.48            ( k1_tarski @ A ) ) <=>
% 0.24/0.48          ( ( A ) != ( B ) ) ) )),
% 0.24/0.48    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.24/0.48  thf('3', plain,
% 0.24/0.48      ((((sk_A) = (sk_B))
% 0.24/0.48        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48            != (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('4', plain,
% 0.24/0.48      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48          != (k1_tarski @ sk_A)))
% 0.24/0.48         <= (~
% 0.24/0.48             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48                = (k1_tarski @ sk_A))))),
% 0.24/0.48      inference('split', [status(esa)], ['3'])).
% 0.24/0.48  thf('5', plain,
% 0.24/0.48      ((((sk_A) != (sk_B))
% 0.24/0.48        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48            = (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('6', plain,
% 0.24/0.48      (~ (((sk_A) = (sk_B))) | 
% 0.24/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48          = (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('split', [status(esa)], ['5'])).
% 0.24/0.48  thf('7', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.24/0.48      inference('split', [status(esa)], ['3'])).
% 0.24/0.48  thf('8', plain,
% 0.24/0.48      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48          = (k1_tarski @ sk_A)))
% 0.24/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48                = (k1_tarski @ sk_A))))),
% 0.24/0.48      inference('split', [status(esa)], ['5'])).
% 0.24/0.48  thf('9', plain,
% 0.24/0.48      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.24/0.48          = (k1_tarski @ sk_A)))
% 0.24/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48                = (k1_tarski @ sk_A))) & 
% 0.24/0.48             (((sk_A) = (sk_B))))),
% 0.24/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.24/0.48  thf('10', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.24/0.48      inference('split', [status(esa)], ['3'])).
% 0.24/0.48  thf('11', plain,
% 0.24/0.48      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.24/0.48          = (k1_tarski @ sk_B)))
% 0.24/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48                = (k1_tarski @ sk_A))) & 
% 0.24/0.48             (((sk_A) = (sk_B))))),
% 0.24/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.48  thf('12', plain,
% 0.24/0.48      (![X0 : $i, X2 : $i]:
% 0.24/0.48         ((r1_xboole_0 @ X0 @ X2) | ((k4_xboole_0 @ X0 @ X2) != (X0)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.24/0.48  thf('13', plain,
% 0.24/0.48      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.24/0.48         | (r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 0.24/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48                = (k1_tarski @ sk_A))) & 
% 0.24/0.48             (((sk_A) = (sk_B))))),
% 0.24/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.48  thf('14', plain,
% 0.24/0.48      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.24/0.48         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48                = (k1_tarski @ sk_A))) & 
% 0.24/0.48             (((sk_A) = (sk_B))))),
% 0.24/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.24/0.48  thf(t16_zfmisc_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.24/0.48          ( ( A ) = ( B ) ) ) ))).
% 0.24/0.48  thf('15', plain,
% 0.24/0.48      (![X9 : $i, X10 : $i]:
% 0.24/0.48         (~ (r1_xboole_0 @ (k1_tarski @ X9) @ (k1_tarski @ X10))
% 0.24/0.48          | ((X9) != (X10)))),
% 0.24/0.48      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.24/0.48  thf('16', plain,
% 0.24/0.48      (![X10 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X10))),
% 0.24/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.24/0.48  thf('17', plain,
% 0.24/0.48      (~
% 0.24/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48          = (k1_tarski @ sk_A))) | 
% 0.24/0.48       ~ (((sk_A) = (sk_B)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['14', '16'])).
% 0.24/0.48  thf('18', plain,
% 0.24/0.48      (~
% 0.24/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48          = (k1_tarski @ sk_A))) | 
% 0.24/0.48       (((sk_A) = (sk_B)))),
% 0.24/0.48      inference('split', [status(esa)], ['3'])).
% 0.24/0.48  thf('19', plain,
% 0.24/0.48      (~
% 0.24/0.48       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48          = (k1_tarski @ sk_A)))),
% 0.24/0.48      inference('sat_resolution*', [status(thm)], ['6', '17', '18'])).
% 0.24/0.48  thf('20', plain,
% 0.24/0.48      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.24/0.48         != (k1_tarski @ sk_A))),
% 0.24/0.48      inference('simpl_trail', [status(thm)], ['4', '19'])).
% 0.24/0.48  thf('21', plain,
% 0.24/0.48      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['2', '20'])).
% 0.24/0.48  thf('22', plain, (((sk_A) = (sk_B))),
% 0.24/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.24/0.48  thf('23', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.24/0.48      inference('split', [status(esa)], ['5'])).
% 0.24/0.48  thf('24', plain, (~ (((sk_A) = (sk_B)))),
% 0.24/0.48      inference('sat_resolution*', [status(thm)], ['6', '17'])).
% 0.24/0.48  thf('25', plain, (((sk_A) != (sk_B))),
% 0.24/0.48      inference('simpl_trail', [status(thm)], ['23', '24'])).
% 0.24/0.48  thf('26', plain, ($false),
% 0.24/0.48      inference('simplify_reflect-', [status(thm)], ['22', '25'])).
% 0.24/0.48  
% 0.24/0.48  % SZS output end Refutation
% 0.24/0.48  
% 0.24/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
