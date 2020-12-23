%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rGrtmX6o5s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  52 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  211 ( 412 expanded)
%              Number of equality atoms :   29 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) )
        = ( k1_tarski @ X4 ) )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X7 @ ( k1_tarski @ X6 ) )
       != X7 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('14',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('16',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('19',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['17','18'])).

thf('20',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['9','19'])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['7','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rGrtmX6o5s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 26 iterations in 0.015s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(t14_mcart_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( r2_hidden @
% 0.20/0.45         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.20/0.45       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.45        ( ( r2_hidden @
% 0.20/0.45            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) ) =>
% 0.20/0.45          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & ( ( k2_mcart_1 @ A ) = ( C ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t14_mcart_1])).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      ((r2_hidden @ sk_A @ 
% 0.20/0.45        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t10_mcart_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.45       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.45         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.45         ((r2_hidden @ (k2_mcart_1 @ X9) @ X11)
% 0.20/0.45          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.45  thf('2', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_C))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t20_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.45         ( k1_tarski @ A ) ) <=>
% 0.20/0.45       ( ( A ) != ( B ) ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X4 : $i, X5 : $i]:
% 0.20/0.45         (((k4_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5))
% 0.20/0.45            = (k1_tarski @ X4))
% 0.20/0.45          | ((X4) = (X5)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.45  thf(t65_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.45       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X6 : $i, X7 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.45          | ((k4_xboole_0 @ X7 @ (k1_tarski @ X6)) != (X7)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.45          | ((X0) = (X1))
% 0.20/0.45          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.45  thf('7', plain, (((sk_C) = (k2_mcart_1 @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.45         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.45      inference('split', [status(esa)], ['8'])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      ((r2_hidden @ sk_A @ 
% 0.20/0.45        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_C)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.45         ((r2_hidden @ (k1_mcart_1 @ X9) @ X10)
% 0.20/0.45          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.45  thf('12', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.45  thf('14', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.20/0.45         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.20/0.45      inference('split', [status(esa)], ['8'])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.45  thf('17', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.45      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.45  thf('18', plain,
% 0.20/0.45      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.45      inference('split', [status(esa)], ['8'])).
% 0.20/0.45  thf('19', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['17', '18'])).
% 0.20/0.45  thf('20', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['9', '19'])).
% 0.20/0.45  thf('21', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['7', '20'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
