%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S2Fy3IEXdv

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:20 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 142 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  385 (1569 expanded)
%              Number of equality atoms :   23 (  97 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B != sk_D )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
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
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_B = sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B = sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','8','17'])).

thf('19',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('23',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','8','17','22'])).

thf('24',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['21','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','8','17','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['25','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S2Fy3IEXdv
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 12:09:45 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 59 iterations in 0.018s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(t129_zfmisc_1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( r2_hidden @
% 0.23/0.49         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.23/0.49       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49        ( ( r2_hidden @
% 0.23/0.49            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.23/0.49          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      ((((sk_B) != (sk_D))
% 0.23/0.49        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 0.23/0.49        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49             (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49           (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))
% 0.23/0.49         <= (~
% 0.23/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.23/0.49      inference('split', [status(esa)], ['0'])).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (~
% 0.23/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))) | 
% 0.23/0.49       ~ (((sk_B) = (sk_D))) | ~ ((r2_hidden @ sk_A @ sk_C_1))),
% 0.23/0.49      inference('split', [status(esa)], ['0'])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (((r2_hidden @ sk_A @ sk_C_1)
% 0.23/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49           (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))
% 0.23/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.23/0.49      inference('split', [status(esa)], ['3'])).
% 0.23/0.49  thf(l54_zfmisc_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.23/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.49         ((r2_hidden @ X6 @ X7)
% 0.23/0.49          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.23/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (((r2_hidden @ sk_A @ sk_C_1))
% 0.23/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 0.23/0.49      inference('split', [status(esa)], ['0'])).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.23/0.49       ~
% 0.23/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))
% 0.23/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.23/0.49      inference('split', [status(esa)], ['3'])).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.49         ((r2_hidden @ X8 @ X9)
% 0.23/0.49          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.23/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.23/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.49  thf(d1_tarski, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.23/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.23/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X0 : $i, X3 : $i]:
% 0.23/0.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.23/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      ((((sk_B) = (sk_D)))
% 0.23/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['11', '13'])).
% 0.23/0.49  thf('15', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.23/0.49      inference('split', [status(esa)], ['0'])).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      ((((sk_B) != (sk_B)))
% 0.23/0.49         <= (~ (((sk_B) = (sk_D))) & 
% 0.23/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49               (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.49  thf('17', plain,
% 0.23/0.49      ((((sk_B) = (sk_D))) | 
% 0.23/0.49       ~
% 0.23/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.23/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.23/0.49  thf('18', plain,
% 0.23/0.49      (~
% 0.23/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.23/0.49      inference('sat_resolution*', [status(thm)], ['2', '8', '17'])).
% 0.23/0.49  thf('19', plain,
% 0.23/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49          (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D)))),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.23/0.49  thf('20', plain,
% 0.23/0.49      ((((sk_B) = (sk_D))
% 0.23/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49           (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('21', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.23/0.49      inference('split', [status(esa)], ['20'])).
% 0.23/0.49  thf('22', plain,
% 0.23/0.49      ((((sk_B) = (sk_D))) | 
% 0.23/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.23/0.49      inference('split', [status(esa)], ['20'])).
% 0.23/0.49  thf('23', plain, ((((sk_B) = (sk_D)))),
% 0.23/0.49      inference('sat_resolution*', [status(thm)], ['2', '8', '17', '22'])).
% 0.23/0.49  thf('24', plain, (((sk_B) = (sk_D))),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['21', '23'])).
% 0.23/0.49  thf('25', plain,
% 0.23/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49          (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_B)))),
% 0.23/0.49      inference('demod', [status(thm)], ['19', '24'])).
% 0.23/0.49  thf('26', plain,
% 0.23/0.49      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.23/0.49      inference('split', [status(esa)], ['3'])).
% 0.23/0.49  thf('27', plain,
% 0.23/0.49      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.23/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.23/0.49         (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ sk_D))))),
% 0.23/0.49      inference('split', [status(esa)], ['3'])).
% 0.23/0.49  thf('28', plain, (((r2_hidden @ sk_A @ sk_C_1))),
% 0.23/0.49      inference('sat_resolution*', [status(thm)], ['2', '8', '17', '27'])).
% 0.23/0.49  thf('29', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['26', '28'])).
% 0.23/0.49  thf('30', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.23/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.49  thf('31', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.49      inference('simplify', [status(thm)], ['30'])).
% 0.23/0.49  thf('32', plain,
% 0.23/0.49      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.23/0.49         ((r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X10))
% 0.23/0.49          | ~ (r2_hidden @ X8 @ X10)
% 0.23/0.49          | ~ (r2_hidden @ X6 @ X7))),
% 0.23/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.23/0.49  thf('33', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X2 @ X1)
% 0.23/0.49          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.23/0.49             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.23/0.49  thf('34', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.23/0.49          (k2_zfmisc_1 @ sk_C_1 @ (k1_tarski @ X0)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['29', '33'])).
% 0.23/0.49  thf('35', plain, ($false), inference('demod', [status(thm)], ['25', '34'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
