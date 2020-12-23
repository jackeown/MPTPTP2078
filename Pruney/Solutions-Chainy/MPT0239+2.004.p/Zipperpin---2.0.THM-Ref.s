%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xc2Zaoskdd

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 196 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  478 (2318 expanded)
%              Number of equality atoms :   41 ( 233 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t34_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
      <=> ( ( A = C )
          & ( B = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != sk_D_1 )
    | ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) )
    | ( sk_B != sk_D_1 )
    | ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
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
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( sk_A = sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('19',plain,
    ( ( sk_B = sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = sk_D_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','12','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('26',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,(
    sk_A = sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','12','22','26'])).

thf('28',plain,(
    sk_A = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B = sk_D_1 )
   <= ( sk_B = sk_D_1 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( sk_B = sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,(
    sk_B = sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['2','12','22','31'])).

thf('33',plain,(
    sk_B = sk_D_1 ),
    inference(simpl_trail,[status(thm)],['30','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ ( k2_zfmisc_1 @ X13 @ X16 ) )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['34','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xc2Zaoskdd
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:18 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 71 iterations in 0.033s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.49  thf(t34_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r2_hidden @
% 0.20/0.49         ( k4_tarski @ A @ B ) @ 
% 0.20/0.49         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( r2_hidden @
% 0.20/0.49            ( k4_tarski @ A @ B ) @ 
% 0.20/0.49            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.49          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((sk_B) != (sk_D_1))
% 0.20/0.49        | ((sk_A) != (sk_C_1))
% 0.20/0.49        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49             (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))
% 0.20/0.49         <= (~
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))) | 
% 0.20/0.49       ~ (((sk_B) = (sk_D_1))) | ~ (((sk_A) = (sk_C_1)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((((sk_A) = (sk_C_1))
% 0.20/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf(l54_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((r2_hidden @ X12 @ X13)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X15)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(d1_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X3 : $i]:
% 0.20/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((((sk_A) = (sk_C_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.49  thf('10', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((sk_A) != (sk_A)))
% 0.20/0.49         <= (~ (((sk_A) = (sk_C_1))) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((((sk_A) = (sk_C_1))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((((sk_A) = (sk_C_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D_1))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((r2_hidden @ X14 @ X15)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X15)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X3 : $i]:
% 0.20/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((((sk_B) = (sk_D_1)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((((sk_B) != (sk_B)))
% 0.20/0.49         <= (~ (((sk_B) = (sk_D_1))) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((((sk_B) = (sk_D_1))) | 
% 0.20/0.49       ~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (~
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '12', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1)))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.20/0.49  thf('25', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      ((((sk_A) = (sk_C_1))) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('27', plain, ((((sk_A) = (sk_C_1)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '12', '22', '26'])).
% 0.20/0.49  thf('28', plain, (((sk_A) = (sk_C_1))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((sk_B) = (sk_D_1))
% 0.20/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain, ((((sk_B) = (sk_D_1))) <= ((((sk_B) = (sk_D_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((((sk_B) = (sk_D_1))) | 
% 0.20/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D_1))))),
% 0.20/0.49      inference('split', [status(esa)], ['29'])).
% 0.20/0.49  thf('32', plain, ((((sk_B) = (sk_D_1)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '12', '22', '31'])).
% 0.20/0.49  thf('33', plain, (((sk_B) = (sk_D_1))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['30', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '28', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.49  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ X12 @ X14) @ (k2_zfmisc_1 @ X13 @ X16))
% 0.20/0.49          | ~ (r2_hidden @ X14 @ X16)
% 0.20/0.49          | ~ (r2_hidden @ X12 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ X1)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.20/0.49             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.49  thf('41', plain, ($false), inference('demod', [status(thm)], ['34', '40'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
