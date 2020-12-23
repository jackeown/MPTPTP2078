%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rEGyDAhuY0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  87 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  420 ( 921 expanded)
%              Number of equality atoms :   19 (  44 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X4 ) ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('10',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X5 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 = X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X9 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ( X7 != X6 ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('25',plain,(
    ! [X6: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X5 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rEGyDAhuY0
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:28:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 93 iterations in 0.045s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(t129_zfmisc_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( r2_hidden @
% 0.22/0.51         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.22/0.51       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51        ( ( r2_hidden @
% 0.22/0.51            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.22/0.51          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((((sk_B) != (sk_D))
% 0.22/0.51        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.22/0.51        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (~ (((sk_B) = (sk_D))) | 
% 0.22/0.51       ~
% 0.22/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))) | 
% 0.22/0.51       ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (((r2_hidden @ sk_A @ sk_C)
% 0.22/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(l54_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((r2_hidden @ X1 @ X2)
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X4)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.51  thf('4', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.22/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('6', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (((r2_hidden @ sk_A @ sk_C)
% 0.22/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.22/0.51      inference('split', [status(esa)], ['7'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((r2_hidden @ X3 @ X4)
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X4)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('11', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.22/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.51         ((r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X5))
% 0.22/0.51          | ~ (r2_hidden @ X3 @ X5)
% 0.22/0.51          | ~ (r2_hidden @ X1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X1 @ X0)
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X1 @ sk_A) @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ sk_B @ sk_A) @ 
% 0.22/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_D) @ sk_C)))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.51  thf(t128_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( r2_hidden @
% 0.22/0.51         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.22/0.51       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.51         (((X7) = (X6))
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 0.22/0.51               (k2_zfmisc_1 @ (k1_tarski @ X6) @ X9)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((((sk_B) = (sk_D)))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      ((((sk_B) != (sk_B)))
% 0.22/0.51         <= (~ (((sk_B) = (sk_D))) & 
% 0.22/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((((sk_B) = (sk_D))) | 
% 0.22/0.51       ~
% 0.22/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.22/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      ((((sk_B) = (sk_D))
% 0.22/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((((sk_B) = (sk_D))) | 
% 0.22/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.22/0.51      inference('split', [status(esa)], ['20'])).
% 0.22/0.51  thf('22', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.22/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('23', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.22/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.22/0.51         ((r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 0.22/0.51           (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10))
% 0.22/0.51          | ~ (r2_hidden @ X8 @ X10)
% 0.22/0.51          | ((X7) != (X6)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X6 : $i, X8 : $i, X10 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X8 @ X10)
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ 
% 0.22/0.51             (k2_zfmisc_1 @ (k1_tarski @ X6) @ X10)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (r2_hidden @ (k4_tarski @ X0 @ sk_A) @ 
% 0.22/0.51          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['23', '25'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         ((r2_hidden @ X1 @ X2)
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X4)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.51  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.51         ((r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X5))
% 0.22/0.51          | ~ (r2_hidden @ X3 @ X5)
% 0.22/0.51          | ~ (r2_hidden @ X1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X2 @ X1)
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.22/0.51             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.22/0.51          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '30'])).
% 0.22/0.51  thf('32', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.22/0.51      inference('split', [status(esa)], ['20'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))) & 
% 0.22/0.51             (((sk_B) = (sk_D))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (~ (((sk_B) = (sk_D))) | 
% 0.22/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.51         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['31', '34'])).
% 0.22/0.51  thf('36', plain, ($false),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['1', '6', '19', '21', '35'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
