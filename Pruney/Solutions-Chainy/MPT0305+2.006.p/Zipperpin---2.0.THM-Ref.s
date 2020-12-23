%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5mc2FoHlhY

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:11 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   55 (  78 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  510 ( 868 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t117_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
          & ~ ( r1_tarski @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t117_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X9 ) )
      | ~ ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( sk_A = k1_xboole_0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
   <= ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('32',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B_1 ) @ ( sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['12','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X7 ) @ ( k2_zfmisc_1 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5mc2FoHlhY
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:22:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 123 iterations in 0.166s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.66  thf(t117_zfmisc_1, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.47/0.66            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.47/0.66          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.66        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66             ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.47/0.66               ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.47/0.66             ( ~( r1_tarski @ B @ C ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t117_zfmisc_1])).
% 0.47/0.66  thf('0', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d3_tarski, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf(t7_xboole_0, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf(l54_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.66     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.47/0.66       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.47/0.66         ((r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X9))
% 0.47/0.66          | ~ (r2_hidden @ X7 @ X9)
% 0.47/0.66          | ~ (r2_hidden @ X5 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0))
% 0.47/0.66          | ~ (r2_hidden @ X2 @ X1)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.47/0.66             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r1_tarski @ X0 @ X1)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.47/0.66             (k2_zfmisc_1 @ X0 @ X2))
% 0.47/0.66          | ((X2) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '4'])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.47/0.66         (k2_zfmisc_1 @ sk_C_1 @ sk_A))
% 0.47/0.66        | (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66           (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.47/0.66         (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 0.47/0.66      inference('split', [status(esa)], ['6'])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | (r2_hidden @ X0 @ X2)
% 0.47/0.66          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))
% 0.47/0.66           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          (((sk_A) = (k1_xboole_0))
% 0.47/0.66           | (r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66           | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.47/0.66              (k2_zfmisc_1 @ sk_C_1 @ sk_A))))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['5', '9'])).
% 0.47/0.66  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66           | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.47/0.66              (k2_zfmisc_1 @ sk_C_1 @ sk_A))))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_C_1 @ sk_A))))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.47/0.66         ((r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X9))
% 0.47/0.66          | ~ (r2_hidden @ X7 @ X9)
% 0.47/0.66          | ~ (r2_hidden @ X5 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X0 @ X1)
% 0.47/0.66          | ~ (r2_hidden @ X3 @ X2)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.47/0.66             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0))
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.47/0.66             (k2_zfmisc_1 @ X0 @ X1))
% 0.47/0.66          | (r1_tarski @ X1 @ X2))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '16'])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66         (k2_zfmisc_1 @ sk_A @ sk_C_1)))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.47/0.66      inference('split', [status(esa)], ['6'])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | (r2_hidden @ X0 @ X2)
% 0.47/0.66          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 0.47/0.66           | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66           | ((sk_A) = (k1_xboole_0))
% 0.47/0.66           | (r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.47/0.66              (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['17', '20'])).
% 0.47/0.66  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66           | (r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.47/0.66              (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.66         ((r2_hidden @ X7 @ X8)
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X8)))),
% 0.47/0.66      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      ((![X0 : $i]:
% 0.47/0.66          ((r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66           | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1)))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      ((((r1_tarski @ sk_B_1 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1)))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (((r1_tarski @ sk_B_1 @ sk_C_1))
% 0.47/0.66         <= (((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66               (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.47/0.66      inference('simplify', [status(thm)], ['27'])).
% 0.47/0.66  thf('29', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (~
% 0.47/0.66       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66         (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.47/0.66         (k2_zfmisc_1 @ sk_C_1 @ sk_A))) | 
% 0.47/0.66       ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ 
% 0.47/0.66         (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.47/0.66      inference('split', [status(esa)], ['6'])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (((r1_tarski @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ 
% 0.47/0.66         (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.47/0.66      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_B_1) @ (sk_B @ sk_A)) @ 
% 0.47/0.66             (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.47/0.66      inference('simpl_trail', [status(thm)], ['12', '32'])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.66         ((r2_hidden @ X5 @ X6)
% 0.47/0.66          | ~ (r2_hidden @ (k4_tarski @ X5 @ X7) @ (k2_zfmisc_1 @ X6 @ X8)))),
% 0.47/0.66      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r1_tarski @ sk_B_1 @ X0)
% 0.47/0.66          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (((r1_tarski @ sk_B_1 @ sk_C_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.66  thf('38', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.47/0.66      inference('simplify', [status(thm)], ['37'])).
% 0.47/0.66  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
