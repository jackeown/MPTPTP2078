%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5nbrOCzaP3

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 201 expanded)
%              Number of leaves         :   13 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  473 (2243 expanded)
%              Number of equality atoms :   31 ( 158 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    | ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X25 ) )
        = ( k1_tarski @ X24 ) )
      | ( X24 = X25 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( sk_A = sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,
    ( ( sk_A = sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','22'])).

thf('24',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('25',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('26',plain,(
    sk_A = sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','14','21','25'])).

thf('27',plain,(
    sk_A = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['24','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ X9 )
        = ( k1_tarski @ X7 ) )
      | ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X24 != X23 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ ( k1_tarski @ X23 ) )
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('31',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X23 ) )
     != ( k1_tarski @ X23 ) ) ),
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
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['34'])).

thf('37',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','14','21','36'])).

thf('38',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5nbrOCzaP3
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:29:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 81 iterations in 0.041s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(t128_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( r2_hidden @
% 0.21/0.50         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.21/0.50       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50        ( ( r2_hidden @
% 0.21/0.50            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.21/0.50          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.21/0.50        | ((sk_A) != (sk_C_1))
% 0.21/0.50        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50             (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))) | 
% 0.21/0.50       ~ ((r2_hidden @ sk_B @ sk_D)) | ~ (((sk_A) = (sk_C_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      ((((sk_A) = (sk_C_1))
% 0.21/0.50        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.21/0.50      inference('split', [status(esa)], ['3'])).
% 0.21/0.50  thf(l54_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((r2_hidden @ X10 @ X11)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf(t20_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.50         ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ( A ) != ( B ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X25))
% 0.21/0.50            = (k1_tarski @ X24))
% 0.21/0.50          | ((X24) = (X25)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.50  thf(l33_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ X7) @ X8) != (k1_tarski @ X7)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.50          | ((X0) = (X1))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((((sk_A) = (sk_C_1)))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '10'])).
% 0.21/0.50  thf('12', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((((sk_A) != (sk_A)))
% 0.21/0.50         <= (~ (((sk_A) = (sk_C_1))) & 
% 0.21/0.50             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((((sk_A) = (sk_C_1))) | 
% 0.21/0.50       ~
% 0.21/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.21/0.50      inference('split', [status(esa)], ['3'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((((sk_A) = (sk_C_1)))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '10'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D)))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((r2_hidden @ X12 @ X13)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ sk_D))
% 0.21/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.21/0.50       ~
% 0.21/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (~
% 0.21/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['2', '14', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50          (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['1', '22'])).
% 0.21/0.50  thf('24', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.21/0.50      inference('split', [status(esa)], ['3'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((((sk_A) = (sk_C_1))) | 
% 0.21/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.21/0.50      inference('split', [status(esa)], ['3'])).
% 0.21/0.50  thf('26', plain, ((((sk_A) = (sk_C_1)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['2', '14', '21', '25'])).
% 0.21/0.50  thf('27', plain, (((sk_A) = (sk_C_1))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['24', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X7 : $i, X9 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ (k1_tarski @ X7) @ X9) = (k1_tarski @ X7))
% 0.21/0.50          | (r2_hidden @ X7 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i]:
% 0.21/0.50         (((X24) != (X23))
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ X24) @ (k1_tarski @ X23))
% 0.21/0.50              != (k1_tarski @ X24)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X23 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X23))
% 0.21/0.50           != (k1_tarski @ X23))),
% 0.21/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.50          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '31'])).
% 0.21/0.50  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ sk_D)
% 0.21/0.50        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.50      inference('split', [status(esa)], ['34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.21/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ sk_D)))),
% 0.21/0.50      inference('split', [status(esa)], ['34'])).
% 0.21/0.50  thf('37', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['2', '14', '21', '36'])).
% 0.21/0.50  thf('38', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.21/0.50         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 0.21/0.50          | ~ (r2_hidden @ X12 @ X14)
% 0.21/0.50          | ~ (r2_hidden @ X10 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.21/0.50          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '40'])).
% 0.21/0.50  thf('42', plain, ($false), inference('demod', [status(thm)], ['28', '41'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
