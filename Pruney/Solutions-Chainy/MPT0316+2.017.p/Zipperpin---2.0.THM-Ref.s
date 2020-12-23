%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.itYK7ANhC9

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 156 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  456 (1719 expanded)
%              Number of equality atoms :   30 ( 119 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t128_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
      <=> ( ( A = C )
          & ( r2_hidden @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['2'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ X33 ) @ ( k2_zfmisc_1 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X38 ) )
        = ( k1_tarski @ X37 ) )
      | ( X37 = X38 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ X33 ) @ ( k2_zfmisc_1 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['13','18','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('23',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,(
    sk_A = sk_C ),
    inference('sat_resolution*',[status(thm)],['13','18','19','23'])).

thf('25',plain,(
    sk_A = sk_C ),
    inference(simpl_trail,[status(thm)],['22','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X28: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X28 ) @ X30 )
        = ( k1_tarski @ X28 ) )
      | ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('28',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37 != X36 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X36 ) )
       != ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('29',plain,(
    ! [X36: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X36 ) )
     != ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    ! [X31: $i,X32: $i,X33: $i,X35: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X31 @ X33 ) @ ( k2_zfmisc_1 @ X32 @ X35 ) )
      | ~ ( r2_hidden @ X33 @ X35 )
      | ~ ( r2_hidden @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['32'])).

thf('37',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['13','18','19','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['26','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.itYK7ANhC9
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 82 iterations in 0.036s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(t128_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r2_hidden @
% 0.20/0.48         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( r2_hidden @
% 0.20/0.48            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.48          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.20/0.48        | ((sk_A) != (sk_C))
% 0.20/0.48        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((sk_A) = (sk_C))
% 0.20/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf(l54_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.48         ((r2_hidden @ X31 @ X32)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X31 @ X33) @ (k2_zfmisc_1 @ X32 @ X34)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf(t20_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.48         ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ( A ) != ( B ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X37 : $i, X38 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X38))
% 0.20/0.48            = (k1_tarski @ X37))
% 0.20/0.48          | ((X37) = (X38)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.48  thf(l33_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X28 : $i, X29 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X28 @ X29)
% 0.20/0.48          | ((k4_xboole_0 @ (k1_tarski @ X28) @ X29) != (k1_tarski @ X28)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.48          | ((X0) = (X1))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((sk_A) = (sk_C)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.49  thf('11', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((((sk_A) != (sk_A)))
% 0.20/0.49         <= (~ (((sk_A) = (sk_C))) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((((sk_A) = (sk_C))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         ((r2_hidden @ X33 @ X34)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X31 @ X33) @ (k2_zfmisc_1 @ X32 @ X34)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ sk_D))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.49       ~ (((sk_A) = (sk_C))) | ~ ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['13', '18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.20/0.49  thf('22', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((((sk_A) = (sk_C))) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['2'])).
% 0.20/0.49  thf('24', plain, ((((sk_A) = (sk_C)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['13', '18', '19', '23'])).
% 0.20/0.49  thf('25', plain, (((sk_A) = (sk_C))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['22', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X28 : $i, X30 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ (k1_tarski @ X28) @ X30) = (k1_tarski @ X28))
% 0.20/0.49          | (r2_hidden @ X28 @ X30))),
% 0.20/0.49      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X36 : $i, X37 : $i]:
% 0.20/0.49         (((X37) != (X36))
% 0.20/0.49          | ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X36))
% 0.20/0.49              != (k1_tarski @ X37)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X36 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X36))
% 0.20/0.49           != (k1_tarski @ X36))),
% 0.20/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '29'])).
% 0.20/0.49  thf('31', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ sk_D)
% 0.20/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i, X35 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ X31 @ X33) @ (k2_zfmisc_1 @ X32 @ X35))
% 0.20/0.49          | ~ (r2_hidden @ X33 @ X35)
% 0.20/0.49          | ~ (r2_hidden @ X31 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((![X0 : $i, X1 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X1 @ X0)
% 0.20/0.49           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.20/0.49         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['32'])).
% 0.20/0.49  thf('37', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['13', '18', '19', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '38'])).
% 0.20/0.49  thf('40', plain, ($false), inference('demod', [status(thm)], ['26', '39'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
