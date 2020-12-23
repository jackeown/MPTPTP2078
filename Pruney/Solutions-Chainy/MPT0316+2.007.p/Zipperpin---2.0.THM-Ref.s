%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.reZl0wSrSW

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:17 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 178 expanded)
%              Number of leaves         :   11 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  411 (2000 expanded)
%              Number of equality atoms :   24 ( 130 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    | ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_A = sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( sk_A = sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['2','12','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('24',plain,(
    sk_A = sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','12','19','23'])).

thf('25',plain,(
    sk_A = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['22','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','12','19','31'])).

thf('33',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ ( k2_zfmisc_1 @ X27 @ X30 ) )
      | ~ ( r2_hidden @ X28 @ X30 )
      | ~ ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['26','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.reZl0wSrSW
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 65 iterations in 0.037s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(t128_zfmisc_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( r2_hidden @
% 0.19/0.48         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.19/0.48       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48        ( ( r2_hidden @
% 0.19/0.48            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.19/0.48          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.19/0.48        | ((sk_A) != (sk_C_1))
% 0.19/0.48        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48             (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))
% 0.19/0.48         <= (~
% 0.19/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (~
% 0.19/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))) | 
% 0.19/0.48       ~ ((r2_hidden @ sk_B @ sk_D)) | ~ (((sk_A) = (sk_C_1)))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      ((((sk_A) = (sk_C_1))
% 0.19/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))
% 0.19/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.19/0.48      inference('split', [status(esa)], ['3'])).
% 0.19/0.48  thf(l54_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.19/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.48         ((r2_hidden @ X26 @ X27)
% 0.19/0.48          | ~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X29)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.19/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf(d1_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X3 : $i]:
% 0.19/0.48         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((((sk_A) = (sk_C_1)))
% 0.19/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.48  thf('10', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      ((((sk_A) != (sk_A)))
% 0.19/0.48         <= (~ (((sk_A) = (sk_C_1))) & 
% 0.19/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      ((((sk_A) = (sk_C_1))) | 
% 0.19/0.48       ~
% 0.19/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))
% 0.19/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.19/0.48      inference('split', [status(esa)], ['3'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      ((((sk_A) = (sk_C_1)))
% 0.19/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D)))
% 0.19/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.48         ((r2_hidden @ X28 @ X29)
% 0.19/0.48          | ~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X29)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (((r2_hidden @ sk_B @ sk_D))
% 0.19/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.19/0.48       ~
% 0.19/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (~
% 0.19/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['2', '12', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48          (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.19/0.48  thf('22', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.19/0.48      inference('split', [status(esa)], ['3'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      ((((sk_A) = (sk_C_1))) | 
% 0.19/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.19/0.48      inference('split', [status(esa)], ['3'])).
% 0.19/0.48  thf('24', plain, ((((sk_A) = (sk_C_1)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['2', '12', '19', '23'])).
% 0.19/0.48  thf('25', plain, (((sk_A) = (sk_C_1))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['22', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D))),
% 0.19/0.48      inference('demod', [status(thm)], ['21', '25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.48  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (((r2_hidden @ sk_B @ sk_D)
% 0.19/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.19/0.48      inference('split', [status(esa)], ['29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.19/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.19/0.48      inference('split', [status(esa)], ['29'])).
% 0.19/0.48  thf('32', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['2', '12', '19', '31'])).
% 0.19/0.48  thf('33', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['30', '32'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 0.19/0.48         ((r2_hidden @ (k4_tarski @ X26 @ X28) @ (k2_zfmisc_1 @ X27 @ X30))
% 0.19/0.48          | ~ (r2_hidden @ X28 @ X30)
% 0.19/0.48          | ~ (r2_hidden @ X26 @ X27))),
% 0.19/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.48          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.19/0.48          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['28', '35'])).
% 0.19/0.48  thf('37', plain, ($false), inference('demod', [status(thm)], ['26', '36'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
