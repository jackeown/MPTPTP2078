%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BDGsanxuNh

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:47 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   37 (  53 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  219 ( 420 expanded)
%              Number of equality atoms :   31 (  59 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t14_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( k2_mcart_1 @ A )
            = C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_mcart_1])).

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('4',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X8 ) )
        = ( k1_tarski @ X7 ) )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X10 @ ( k1_tarski @ X9 ) )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,
    ( ( sk_C != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,
    ( $false
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('14',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('16',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['11','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BDGsanxuNh
% 0.14/0.38  % Computer   : n006.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 12:52:23 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 28 iterations in 0.017s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.23/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(t14_mcart_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( r2_hidden @
% 0.23/0.50         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.23/0.50       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.50        ( ( r2_hidden @
% 0.23/0.50            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.23/0.50          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t14_mcart_1])).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.23/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.23/0.50      inference('split', [status(esa)], ['0'])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      ((r2_hidden @ sk_A @ 
% 0.23/0.50        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t10_mcart_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.23/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.23/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.50         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.23/0.50          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.50  thf('4', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))),
% 0.23/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.50  thf(t20_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.23/0.50         ( k1_tarski @ A ) ) <=>
% 0.23/0.50       ( ( A ) != ( B ) ) ))).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i]:
% 0.23/0.50         (((k4_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X8))
% 0.23/0.50            = (k1_tarski @ X7))
% 0.23/0.50          | ((X7) = (X8)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.23/0.50  thf(t65_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.23/0.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X9 : $i, X10 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X9 @ X10)
% 0.23/0.50          | ((k4_xboole_0 @ X10 @ (k1_tarski @ X9)) != (X10)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.23/0.50          | ((X0) = (X1))
% 0.23/0.50          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.23/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.23/0.50  thf('9', plain, (((sk_C) = (k2_mcart_1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['4', '8'])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      ((((sk_C) != (sk_C))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.23/0.50      inference('demod', [status(thm)], ['1', '9'])).
% 0.23/0.50  thf('11', plain, (($false) <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.23/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      ((r2_hidden @ sk_A @ 
% 0.23/0.50        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.50         ((r2_hidden @ (k1_mcart_1 @ X12) @ X13)
% 0.23/0.50          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.23/0.50  thf('14', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.23/0.50      inference('simplify', [status(thm)], ['7'])).
% 0.23/0.50  thf('16', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.23/0.50         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.23/0.50      inference('split', [status(esa)], ['0'])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.50  thf('19', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.23/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.23/0.50      inference('split', [status(esa)], ['0'])).
% 0.23/0.50  thf('21', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.23/0.50      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.23/0.50  thf('22', plain, ($false),
% 0.23/0.50      inference('simpl_trail', [status(thm)], ['11', '21'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
