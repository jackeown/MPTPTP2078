%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k2nFtDl1Kc

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 201 expanded)
%              Number of leaves         :   13 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  470 (2229 expanded)
%              Number of equality atoms :   31 ( 158 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) )
        = ( k1_tarski @ X22 ) )
      | ( X22 = X23 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( ( k4_xboole_0 @ X34 @ ( k1_tarski @ X33 ) )
       != X34 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( sk_C = sk_A )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,
    ( ( sk_C = sk_A )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','22'])).

thf('24',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('25',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('26',plain,(
    sk_A = sk_C ),
    inference('sat_resolution*',[status(thm)],['2','14','21','25'])).

thf('27',plain,(
    sk_A = sk_C ),
    inference(simpl_trail,[status(thm)],['24','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) )
        = X34 )
      | ( r2_hidden @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 != X21 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X21 ) )
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('31',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X21 ) )
     != ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['34'])).

thf('37',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','14','21','36'])).

thf('38',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X11 ) )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['28','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k2nFtDl1Kc
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:17:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 101 iterations in 0.042s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(t128_zfmisc_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( r2_hidden @
% 0.19/0.49         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.19/0.49       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49        ( ( r2_hidden @
% 0.19/0.49            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.19/0.49          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.19/0.49        | ((sk_A) != (sk_C))
% 0.19/0.49        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (~
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.19/0.49       ~ ((r2_hidden @ sk_B @ sk_D)) | ~ (((sk_A) = (sk_C)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      ((((sk_A) = (sk_C))
% 0.19/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.49      inference('split', [status(esa)], ['3'])).
% 0.19/0.49  thf(l54_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.19/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.49         ((r2_hidden @ X7 @ X8)
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf(t20_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.49         ( k1_tarski @ A ) ) <=>
% 0.19/0.49       ( ( A ) != ( B ) ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X22 : $i, X23 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23))
% 0.19/0.49            = (k1_tarski @ X22))
% 0.19/0.49          | ((X22) = (X23)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.49  thf(t65_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.19/0.49       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X33 : $i, X34 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X33 @ X34)
% 0.19/0.49          | ((k4_xboole_0 @ X34 @ (k1_tarski @ X33)) != (X34)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.19/0.49          | ((X0) = (X1))
% 0.19/0.49          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((((sk_C) = (sk_A)))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '10'])).
% 0.19/0.49  thf('12', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      ((((sk_A) != (sk_A)))
% 0.19/0.49         <= (~ (((sk_A) = (sk_C))) & 
% 0.19/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      ((((sk_A) = (sk_C))) | 
% 0.19/0.49       ~
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.49      inference('split', [status(esa)], ['3'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      ((((sk_C) = (sk_A)))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '10'])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D)))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.49         ((r2_hidden @ X9 @ X10)
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (((r2_hidden @ sk_B @ sk_D))
% 0.19/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.19/0.49       ~
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (~
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['2', '14', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['1', '22'])).
% 0.19/0.49  thf('24', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.19/0.49      inference('split', [status(esa)], ['3'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((((sk_A) = (sk_C))) | 
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['3'])).
% 0.19/0.49  thf('26', plain, ((((sk_A) = (sk_C)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['2', '14', '21', '25'])).
% 0.19/0.49  thf('27', plain, (((sk_A) = (sk_C))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['24', '26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['23', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X34 : $i, X35 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ X34 @ (k1_tarski @ X35)) = (X34))
% 0.19/0.49          | (r2_hidden @ X35 @ X34))),
% 0.19/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i]:
% 0.19/0.49         (((X22) != (X21))
% 0.19/0.49          | ((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X21))
% 0.19/0.49              != (k1_tarski @ X22)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X21 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X21))
% 0.19/0.49           != (k1_tarski @ X21))),
% 0.19/0.49      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.19/0.49          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['29', '31'])).
% 0.19/0.49  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (((r2_hidden @ sk_B @ sk_D)
% 0.19/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.19/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['34'])).
% 0.19/0.49  thf('37', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['2', '14', '21', '36'])).
% 0.19/0.49  thf('38', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.19/0.49         ((r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X11))
% 0.19/0.49          | ~ (r2_hidden @ X9 @ X11)
% 0.19/0.49          | ~ (r2_hidden @ X7 @ X8))),
% 0.19/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.19/0.49          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['33', '40'])).
% 0.19/0.49  thf('42', plain, ($false), inference('demod', [status(thm)], ['28', '41'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
