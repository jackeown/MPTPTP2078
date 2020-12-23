%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mghShT7FFg

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:45 EST 2020

% Result     : Theorem 0.26s
% Output     : Refutation 0.26s
% Verified   : 
% Statistics : Number of formulae       :   59 (  93 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   18
%              Number of atoms          :  412 ( 853 expanded)
%              Number of equality atoms :   21 (  37 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_D )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_B @ sk_D ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_C_1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','30'])).

thf('32',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('34',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['16','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['14','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','38','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mghShT7FFg
% 0.15/0.38  % Computer   : n014.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 11:43:52 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.26/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.26/0.51  % Solved by: fo/fo7.sh
% 0.26/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.26/0.51  % done 82 iterations in 0.049s
% 0.26/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.26/0.51  % SZS output start Refutation
% 0.26/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.26/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.26/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.26/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.26/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.26/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.26/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.26/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.26/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.26/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.26/0.51  thf(t138_zfmisc_1, conjecture,
% 0.26/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.26/0.51     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.26/0.51       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.26/0.51         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.26/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.26/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.26/0.51        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.26/0.51          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.26/0.51            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.26/0.51    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.26/0.51  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.26/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.51  thf(d3_tarski, axiom,
% 0.26/0.51    (![A:$i,B:$i]:
% 0.26/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.26/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.26/0.51  thf('1', plain,
% 0.26/0.51      (![X1 : $i, X3 : $i]:
% 0.26/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.26/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.26/0.51  thf('2', plain,
% 0.26/0.51      (![X1 : $i, X3 : $i]:
% 0.26/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.26/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.26/0.51  thf(l54_zfmisc_1, axiom,
% 0.26/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.26/0.51     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.26/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.26/0.51  thf('3', plain,
% 0.26/0.51      (![X4 : $i, X5 : $i, X6 : $i, X8 : $i]:
% 0.26/0.51         ((r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X8))
% 0.26/0.51          | ~ (r2_hidden @ X6 @ X8)
% 0.26/0.51          | ~ (r2_hidden @ X4 @ X5))),
% 0.26/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.26/0.51  thf('4', plain,
% 0.26/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.51         ((r1_tarski @ X0 @ X1)
% 0.26/0.51          | ~ (r2_hidden @ X3 @ X2)
% 0.26/0.51          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.26/0.51             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.26/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.26/0.51  thf('5', plain,
% 0.26/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.26/0.51         ((r1_tarski @ X0 @ X1)
% 0.26/0.51          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.26/0.51             (k2_zfmisc_1 @ X0 @ X2))
% 0.26/0.51          | (r1_tarski @ X2 @ X3))),
% 0.26/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.26/0.51  thf('6', plain,
% 0.26/0.51      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.26/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.51  thf('7', plain,
% 0.26/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.26/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.26/0.51          | (r2_hidden @ X0 @ X2)
% 0.26/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.26/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.26/0.51  thf('8', plain,
% 0.26/0.51      (![X0 : $i]:
% 0.26/0.51         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.26/0.51          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.26/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.26/0.51  thf('9', plain,
% 0.26/0.51      (![X0 : $i, X1 : $i]:
% 0.26/0.51         ((r1_tarski @ sk_B @ X0)
% 0.26/0.51          | (r1_tarski @ sk_A @ X1)
% 0.26/0.51          | (r2_hidden @ 
% 0.26/0.51             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.26/0.51             (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.26/0.51      inference('sup-', [status(thm)], ['5', '8'])).
% 0.26/0.51  thf('10', plain,
% 0.26/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.26/0.51         ((r2_hidden @ X6 @ X7)
% 0.26/0.51          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 0.26/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.26/0.51  thf('11', plain,
% 0.26/0.51      (![X0 : $i, X1 : $i]:
% 0.26/0.51         ((r1_tarski @ sk_A @ X1)
% 0.26/0.51          | (r1_tarski @ sk_B @ X0)
% 0.26/0.51          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_D))),
% 0.26/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.26/0.51  thf('12', plain,
% 0.26/0.51      (![X1 : $i, X3 : $i]:
% 0.26/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.26/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.26/0.51  thf('13', plain,
% 0.26/0.51      (![X0 : $i]:
% 0.26/0.51         ((r1_tarski @ sk_B @ sk_D)
% 0.26/0.51          | (r1_tarski @ sk_A @ X0)
% 0.26/0.51          | (r1_tarski @ sk_B @ sk_D))),
% 0.26/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.26/0.51  thf('14', plain,
% 0.26/0.51      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (r1_tarski @ sk_B @ sk_D))),
% 0.26/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.26/0.51  thf('15', plain,
% 0.26/0.51      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.26/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.51  thf('16', plain,
% 0.26/0.51      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.26/0.51      inference('split', [status(esa)], ['15'])).
% 0.26/0.51  thf('17', plain,
% 0.26/0.51      (![X0 : $i, X1 : $i]:
% 0.26/0.51         ((r1_tarski @ sk_B @ X0)
% 0.26/0.51          | (r1_tarski @ sk_A @ X1)
% 0.26/0.51          | (r2_hidden @ 
% 0.26/0.51             (k4_tarski @ (sk_C @ X1 @ sk_A) @ (sk_C @ X0 @ sk_B)) @ 
% 0.26/0.51             (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.26/0.51      inference('sup-', [status(thm)], ['5', '8'])).
% 0.26/0.51  thf('18', plain,
% 0.26/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.26/0.51         ((r2_hidden @ X4 @ X5)
% 0.26/0.51          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 0.26/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.26/0.51  thf('19', plain,
% 0.26/0.51      (![X0 : $i, X1 : $i]:
% 0.26/0.51         ((r1_tarski @ sk_A @ X1)
% 0.26/0.51          | (r1_tarski @ sk_B @ X0)
% 0.26/0.51          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_C_1))),
% 0.26/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.26/0.51  thf('20', plain,
% 0.26/0.51      (![X1 : $i, X3 : $i]:
% 0.26/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.26/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.26/0.51  thf('21', plain,
% 0.26/0.51      (![X0 : $i]:
% 0.26/0.51         ((r1_tarski @ sk_B @ X0)
% 0.26/0.51          | (r1_tarski @ sk_A @ sk_C_1)
% 0.26/0.51          | (r1_tarski @ sk_A @ sk_C_1))),
% 0.26/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.26/0.51  thf('22', plain,
% 0.26/0.51      (![X0 : $i]: ((r1_tarski @ sk_A @ sk_C_1) | (r1_tarski @ sk_B @ X0))),
% 0.26/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.26/0.51  thf('23', plain,
% 0.26/0.51      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.26/0.51      inference('split', [status(esa)], ['15'])).
% 0.26/0.51  thf('24', plain,
% 0.26/0.51      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 0.26/0.51         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.26/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.26/0.51  thf(t135_zfmisc_1, axiom,
% 0.26/0.51    (![A:$i,B:$i]:
% 0.26/0.51     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.26/0.51         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.26/0.51       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.26/0.51  thf('25', plain,
% 0.26/0.51      (![X12 : $i, X13 : $i]:
% 0.26/0.51         (((X12) = (k1_xboole_0))
% 0.26/0.51          | ~ (r1_tarski @ X12 @ (k2_zfmisc_1 @ X12 @ X13)))),
% 0.26/0.51      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.26/0.51  thf('26', plain,
% 0.26/0.51      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.26/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.26/0.51  thf('27', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.26/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.51  thf('28', plain,
% 0.26/0.51      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.26/0.51         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.26/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.26/0.51  thf(t113_zfmisc_1, axiom,
% 0.26/0.51    (![A:$i,B:$i]:
% 0.26/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.26/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.26/0.51  thf('29', plain,
% 0.26/0.51      (![X10 : $i, X11 : $i]:
% 0.26/0.51         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.26/0.51          | ((X11) != (k1_xboole_0)))),
% 0.26/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.26/0.51  thf('30', plain,
% 0.26/0.51      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.26/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.26/0.51  thf('31', plain,
% 0.26/0.51      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.26/0.51      inference('demod', [status(thm)], ['28', '30'])).
% 0.26/0.51  thf('32', plain, (((r1_tarski @ sk_A @ sk_C_1))),
% 0.26/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.26/0.51  thf('33', plain,
% 0.26/0.51      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C_1))),
% 0.26/0.51      inference('split', [status(esa)], ['15'])).
% 0.26/0.51  thf('34', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 0.26/0.51      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.26/0.51  thf('35', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.26/0.51      inference('simpl_trail', [status(thm)], ['16', '34'])).
% 0.26/0.51  thf('36', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.26/0.51      inference('clc', [status(thm)], ['14', '35'])).
% 0.26/0.51  thf('37', plain,
% 0.26/0.51      (![X12 : $i, X13 : $i]:
% 0.26/0.51         (((X12) = (k1_xboole_0))
% 0.26/0.51          | ~ (r1_tarski @ X12 @ (k2_zfmisc_1 @ X12 @ X13)))),
% 0.26/0.51      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.26/0.51  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.26/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.26/0.51  thf('39', plain,
% 0.26/0.51      (![X10 : $i, X11 : $i]:
% 0.26/0.51         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.26/0.51          | ((X10) != (k1_xboole_0)))),
% 0.26/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.26/0.51  thf('40', plain,
% 0.26/0.51      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.26/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.26/0.51  thf('41', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.26/0.51      inference('demod', [status(thm)], ['0', '38', '40'])).
% 0.26/0.51  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.26/0.51  
% 0.26/0.51  % SZS output end Refutation
% 0.26/0.51  
% 0.26/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
