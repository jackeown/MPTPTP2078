%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DvhhSucvOM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 156 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  444 (1702 expanded)
%              Number of equality atoms :   30 ( 113 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X8 ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X8 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) )
        = ( k1_tarski @ X20 ) )
      | ( X20 = X21 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( ( k4_xboole_0 @ X30 @ ( k1_tarski @ X29 ) )
       != X30 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ X30 @ ( k1_tarski @ X31 ) )
        = X30 )
      | ( r2_hidden @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 != X19 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X19 ) )
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('34',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) )
     != ( k1_tarski @ X19 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X9 ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DvhhSucvOM
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 114 iterations in 0.041s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(t129_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r2_hidden @
% 0.20/0.49         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.49       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( r2_hidden @
% 0.20/0.49            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.49          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((sk_B) != (sk_D))
% 0.20/0.49        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.20/0.49        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))) | 
% 0.20/0.49       ~ (((sk_B) = (sk_D))) | ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ sk_C)
% 0.20/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf(l54_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         ((r2_hidden @ X5 @ X6)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ sk_C))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.49         ((r2_hidden @ X7 @ X8)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(t20_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.49         ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ( A ) != ( B ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21))
% 0.20/0.49            = (k1_tarski @ X20))
% 0.20/0.49          | ((X20) = (X21)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.49  thf(t65_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.49       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X29 : $i, X30 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X29 @ X30)
% 0.20/0.49          | ((k4_xboole_0 @ X30 @ (k1_tarski @ X29)) != (X30)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.49          | ((X0) = (X1))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((((sk_D) = (sk_B)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '15'])).
% 0.20/0.49  thf('17', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((((sk_B) != (sk_B)))
% 0.20/0.49         <= (~ (((sk_B) = (sk_D))) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((((sk_B) = (sk_D))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '8', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((((sk_B) = (sk_D))
% 0.20/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((((sk_B) = (sk_D))) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['22'])).
% 0.20/0.49  thf('25', plain, ((((sk_B) = (sk_D)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '8', '19', '24'])).
% 0.20/0.49  thf('26', plain, (((sk_B) = (sk_D))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['23', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('30', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '8', '19', '29'])).
% 0.20/0.49  thf('31', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X30 : $i, X31 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X30 @ (k1_tarski @ X31)) = (X30))
% 0.20/0.49          | (r2_hidden @ X31 @ X30))),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i]:
% 0.20/0.49         (((X20) != (X19))
% 0.20/0.49          | ((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X19))
% 0.20/0.49              != (k1_tarski @ X20)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X19 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))
% 0.20/0.49           != (k1_tarski @ X19))),
% 0.20/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.49          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '34'])).
% 0.20/0.49  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X9))
% 0.20/0.49          | ~ (r2_hidden @ X7 @ X9)
% 0.20/0.49          | ~ (r2_hidden @ X5 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ X1)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.20/0.49             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.20/0.49          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '38'])).
% 0.20/0.49  thf('40', plain, ($false), inference('demod', [status(thm)], ['27', '39'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
