%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HmmgkcKaMO

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 156 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  444 (1702 expanded)
%              Number of equality atoms :   30 ( 113 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t129_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( B = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != sk_D )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B != sk_D )
    | ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
        = ( k1_tarski @ X12 ) )
      | ( X12 = X13 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( ( k4_xboole_0 @ X15 @ ( k1_tarski @ X14 ) )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_D = sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B = sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','8','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['22'])).

thf('25',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','8','19','24'])).

thf('26',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['23','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','8','19','29'])).

thf('31',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ ( k1_tarski @ X16 ) )
        = X15 )
      | ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 != X11 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X11 ) )
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X11 ) )
     != ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['27','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HmmgkcKaMO
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:52:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 76 iterations in 0.020s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(t129_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @
% 0.21/0.48         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.48       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( r2_hidden @
% 0.21/0.48            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.48          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((sk_B) != (sk_D))
% 0.21/0.48        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.21/0.48        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))) | 
% 0.21/0.48       ~ (((sk_B) = (sk_D))) | ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ sk_C)
% 0.21/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf(l54_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         ((r2_hidden @ X6 @ X7)
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ sk_C))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.48       ~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         ((r2_hidden @ X8 @ X9)
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf(t20_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.48         ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ( A ) != ( B ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13))
% 0.21/0.48            = (k1_tarski @ X12))
% 0.21/0.48          | ((X12) = (X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.48  thf(t65_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.48       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X14 @ X15)
% 0.21/0.48          | ((k4_xboole_0 @ X15 @ (k1_tarski @ X14)) != (X15)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.48          | ((X0) = (X1))
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((sk_D) = (sk_B)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '15'])).
% 0.21/0.48  thf('17', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((((sk_B) != (sk_B)))
% 0.21/0.48         <= (~ (((sk_B) = (sk_D))) & 
% 0.21/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((sk_B) = (sk_D))) | 
% 0.21/0.48       ~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '8', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((((sk_B) = (sk_D))
% 0.21/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((((sk_B) = (sk_D))) | 
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['22'])).
% 0.21/0.48  thf('25', plain, ((((sk_B) = (sk_D)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '8', '19', '24'])).
% 0.21/0.48  thf('26', plain, (((sk_B) = (sk_D))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['23', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('30', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '8', '19', '29'])).
% 0.21/0.48  thf('31', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ X15 @ (k1_tarski @ X16)) = (X15))
% 0.21/0.48          | (r2_hidden @ X16 @ X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (((X12) != (X11))
% 0.21/0.48          | ((k4_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X11))
% 0.21/0.48              != (k1_tarski @ X12)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X11))
% 0.21/0.48           != (k1_tarski @ X11))),
% 0.21/0.48      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.48          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['32', '34'])).
% 0.21/0.48  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X10))
% 0.21/0.48          | ~ (r2_hidden @ X8 @ X10)
% 0.21/0.48          | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X1)
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.21/0.48             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.21/0.48          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['31', '38'])).
% 0.21/0.48  thf('40', plain, ($false), inference('demod', [status(thm)], ['27', '39'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
