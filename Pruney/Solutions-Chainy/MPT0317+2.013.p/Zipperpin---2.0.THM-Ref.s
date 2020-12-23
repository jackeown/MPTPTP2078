%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gSCVbHdnrL

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  87 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  420 ( 921 expanded)
%              Number of equality atoms :   19 (  44 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ( ( sk_B != sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
    | ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_A ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_D ) @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('16',plain,
    ( ( sk_B = sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('20',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['2','3'])).

thf('23',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['2','3'])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ( X12 != X11 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('25',plain,(
    ! [X11: $i,X13: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X15 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
      & ( sk_B = sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B != sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','6','19','21','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gSCVbHdnrL
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 100 iterations in 0.057s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(t129_zfmisc_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( r2_hidden @
% 0.21/0.51         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.51       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51        ( ( r2_hidden @
% 0.21/0.51            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.51          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((((sk_B) != (sk_D))
% 0.21/0.51        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.21/0.51        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (~ (((sk_B) = (sk_D))) | 
% 0.21/0.51       ~
% 0.21/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))) | 
% 0.21/0.51       ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ sk_C)
% 0.21/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(l54_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((r2_hidden @ X6 @ X7)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('4', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('6', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((r2_hidden @ sk_A @ sk_C)
% 0.21/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.51      inference('split', [status(esa)], ['7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((r2_hidden @ X8 @ X9)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf('11', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X10))
% 0.21/0.51          | ~ (r2_hidden @ X8 @ X10)
% 0.21/0.51          | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X1 @ sk_A) @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (((r2_hidden @ (k4_tarski @ sk_B @ sk_A) @ 
% 0.21/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_D) @ sk_C)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.51  thf(t128_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( r2_hidden @
% 0.21/0.51         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.21/0.51       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.51         (((X12) = (X11))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 0.21/0.51               (k2_zfmisc_1 @ (k1_tarski @ X11) @ X14)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((((sk_B) = (sk_D)))
% 0.21/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      ((((sk_B) != (sk_B)))
% 0.21/0.51         <= (~ (((sk_B) = (sk_D))) & 
% 0.21/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((((sk_B) = (sk_D))) | 
% 0.21/0.51       ~
% 0.21/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((((sk_B) = (sk_D))
% 0.21/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      ((((sk_B) = (sk_D))) | 
% 0.21/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['20'])).
% 0.21/0.51  thf('22', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('23', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 0.21/0.51           (k2_zfmisc_1 @ (k1_tarski @ X11) @ X15))
% 0.21/0.51          | ~ (r2_hidden @ X13 @ X15)
% 0.21/0.51          | ((X12) != (X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X11 : $i, X13 : $i, X15 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X13 @ X15)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 0.21/0.51             (k2_zfmisc_1 @ (k1_tarski @ X11) @ X15)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ 
% 0.21/0.51          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         ((r2_hidden @ X6 @ X7)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.51         ((r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X10))
% 0.21/0.51          | ~ (r2_hidden @ X8 @ X10)
% 0.21/0.51          | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ X1)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.21/0.51             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.21/0.51          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '30'])).
% 0.21/0.51  thf('32', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['20'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))
% 0.21/0.51         <= (~
% 0.21/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))) & 
% 0.21/0.51             (((sk_B) = (sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (~ (((sk_B) = (sk_D))) | 
% 0.21/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '34'])).
% 0.21/0.51  thf('36', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['1', '6', '19', '21', '35'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
