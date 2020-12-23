%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XXHIxFMrKN

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  82 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  321 ( 807 expanded)
%              Number of equality atoms :   54 ( 139 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
      | ( X12 = X13 ) ) ),
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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('15',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['8','16'])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XXHIxFMrKN
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 39 iterations in 0.020s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(t17_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) != ( B ) ) =>
% 0.20/0.47       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13))
% 0.20/0.47          | ((X12) = (X13)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.20/0.47  thf(t83_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((X1) = (X0))
% 0.20/0.47          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.47              = (k1_tarski @ X1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf(t20_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.47         ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ( A ) != ( B ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.47            ( k1_tarski @ A ) ) <=>
% 0.20/0.47          ( ( A ) != ( B ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((((sk_A) = (sk_B))
% 0.20/0.47        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47            != (k1_tarski @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47          != (k1_tarski @ sk_A)))
% 0.20/0.47         <= (~
% 0.20/0.47             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47                = (k1_tarski @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      ((((sk_A) != (sk_B))
% 0.20/0.47        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47            = (k1_tarski @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (~ (((sk_A) = (sk_B))) | 
% 0.20/0.47       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47          = (k1_tarski @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['5'])).
% 0.20/0.47  thf(d1_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.47  thf('8', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.20/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.47  thf('9', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['3'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47          = (k1_tarski @ sk_A)))
% 0.20/0.47         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47                = (k1_tarski @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['5'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.20/0.47          = (k1_tarski @ sk_A)))
% 0.20/0.47         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47                = (k1_tarski @ sk_A))) & 
% 0.20/0.47             (((sk_A) = (sk_B))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['3'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.20/0.47          = (k1_tarski @ sk_B)))
% 0.20/0.47         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47                = (k1_tarski @ sk_A))) & 
% 0.20/0.47             (((sk_A) = (sk_B))))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf(l33_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.47          | ((k4_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_tarski @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.20/0.47         | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))))
% 0.20/0.47         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47                = (k1_tarski @ sk_A))) & 
% 0.20/0.47             (((sk_A) = (sk_B))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))
% 0.20/0.47         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47                = (k1_tarski @ sk_A))) & 
% 0.20/0.47             (((sk_A) = (sk_B))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47          = (k1_tarski @ sk_A))) | 
% 0.20/0.47       ~ (((sk_A) = (sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47          = (k1_tarski @ sk_A))) | 
% 0.20/0.47       (((sk_A) = (sk_B)))),
% 0.20/0.47      inference('split', [status(esa)], ['3'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (~
% 0.20/0.47       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47          = (k1_tarski @ sk_A)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['6', '17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.47         != (k1_tarski @ sk_A))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['4', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '20'])).
% 0.20/0.47  thf('22', plain, (((sk_A) = (sk_B))),
% 0.20/0.47      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.47  thf('23', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.20/0.47      inference('split', [status(esa)], ['5'])).
% 0.20/0.47  thf('24', plain, (~ (((sk_A) = (sk_B)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['6', '17'])).
% 0.20/0.47  thf('25', plain, (((sk_A) != (sk_B))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['22', '25'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
