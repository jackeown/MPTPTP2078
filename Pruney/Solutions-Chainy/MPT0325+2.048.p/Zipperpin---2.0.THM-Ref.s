%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FxbEUMLegy

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  88 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  444 ( 789 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

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
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X9 ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
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
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X9 ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C_1 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','34'])).

thf('36',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['16','38'])).

thf('40',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['14','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','40','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FxbEUMLegy
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 122 iterations in 0.097s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.55  thf(t138_zfmisc_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.21/0.55       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.55         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.21/0.55          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.55            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.21/0.55  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t7_xboole_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.55  thf(d3_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf(l54_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.55         ((r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X9))
% 0.21/0.55          | ~ (r2_hidden @ X7 @ X9)
% 0.21/0.55          | ~ (r2_hidden @ X5 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (r2_hidden @ X3 @ X2)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.21/0.55             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((X0) = (k1_xboole_0))
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.21/0.55             (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.55          | (r1_tarski @ X1 @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.55        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r2_hidden @ X0 @ X2)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.21/0.55          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ sk_B_1 @ X0)
% 0.21/0.55          | ((sk_A) = (k1_xboole_0))
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.21/0.55             (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         ((r2_hidden @ X7 @ X8)
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X8)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_A) = (k1_xboole_0))
% 0.21/0.55          | (r1_tarski @ sk_B_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_D))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (((r1_tarski @ sk_B_1 @ sk_D)
% 0.21/0.55        | ((sk_A) = (k1_xboole_0))
% 0.21/0.55        | (r1_tarski @ sk_B_1 @ sk_D))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain, ((((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_D))),
% 0.21/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_A @ sk_C_1) | ~ (r1_tarski @ sk_B_1 @ sk_D))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_B_1 @ sk_D)) <= (~ ((r1_tarski @ sk_B_1 @ sk_D)))),
% 0.21/0.55      inference('split', [status(esa)], ['15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.21/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.55         ((r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X9))
% 0.21/0.55          | ~ (r2_hidden @ X7 @ X9)
% 0.21/0.55          | ~ (r2_hidden @ X5 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((X0) = (k1_xboole_0))
% 0.21/0.55          | ~ (r2_hidden @ X2 @ X1)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.21/0.55             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((r1_tarski @ X0 @ X1)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.21/0.55             (k2_zfmisc_1 @ X0 @ X2))
% 0.21/0.55          | ((X2) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.21/0.55          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_B_1) = (k1_xboole_0))
% 0.21/0.55          | (r1_tarski @ sk_A @ X0)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.55             (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         ((r2_hidden @ X5 @ X6)
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X8)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ sk_A @ X0)
% 0.21/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.55        | (r1_tarski @ sk_A @ sk_C_1)
% 0.21/0.55        | (r1_tarski @ sk_A @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (((r1_tarski @ sk_A @ sk_C_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.21/0.55      inference('split', [status(esa)], ['15'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      ((((sk_B_1) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('31', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.55         <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf(t113_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.21/0.55          | ((X12) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['32', '34'])).
% 0.21/0.55  thf('36', plain, (((r1_tarski @ sk_A @ sk_C_1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (~ ((r1_tarski @ sk_B_1 @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C_1))),
% 0.21/0.55      inference('split', [status(esa)], ['15'])).
% 0.21/0.55  thf('38', plain, (~ ((r1_tarski @ sk_B_1 @ sk_D))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.21/0.55  thf('39', plain, (~ (r1_tarski @ sk_B_1 @ sk_D)),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['16', '38'])).
% 0.21/0.55  thf('40', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('clc', [status(thm)], ['14', '39'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.21/0.55          | ((X11) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.55  thf('43', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '40', '42'])).
% 0.21/0.55  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
