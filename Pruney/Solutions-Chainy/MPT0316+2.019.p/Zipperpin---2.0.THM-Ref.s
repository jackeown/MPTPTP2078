%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tZja0JE34M

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 213 expanded)
%              Number of leaves         :   15 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  502 (2299 expanded)
%              Number of equality atoms :   35 ( 168 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
        = ( k1_tarski @ X12 ) )
      | ( X12 = X13 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( ( k4_xboole_0 @ X15 @ ( k1_tarski @ X14 ) )
       != X15 ) ) ),
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('26',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,(
    sk_A = sk_C ),
    inference('sat_resolution*',[status(thm)],['2','14','22','26'])).

thf('28',plain,(
    sk_A = sk_C ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ ( k1_tarski @ X16 ) )
        = X15 )
      | ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 != X11 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X11 ) )
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X11 ) )
     != ( k1_tarski @ X11 ) ) ),
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
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['38'])).

thf('41',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','14','22','40'])).

thf('42',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['30','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tZja0JE34M
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:38:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 82 iterations in 0.037s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(t128_zfmisc_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( r2_hidden @
% 0.19/0.51         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.19/0.51       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51        ( ( r2_hidden @
% 0.19/0.51            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.19/0.51          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.19/0.51        | ((sk_A) != (sk_C))
% 0.19/0.51        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.19/0.51         <= (~
% 0.19/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (~
% 0.19/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.19/0.51       ~ ((r2_hidden @ sk_B @ sk_D)) | ~ (((sk_A) = (sk_C)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      ((((sk_A) = (sk_C))
% 0.19/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.19/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.51      inference('split', [status(esa)], ['3'])).
% 0.19/0.51  thf(l54_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.19/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.51         ((r2_hidden @ X6 @ X7)
% 0.19/0.51          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.19/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.19/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.51  thf(t20_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.51         ( k1_tarski @ A ) ) <=>
% 0.19/0.51       ( ( A ) != ( B ) ) ))).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X12 : $i, X13 : $i]:
% 0.19/0.51         (((k4_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13))
% 0.19/0.51            = (k1_tarski @ X12))
% 0.19/0.51          | ((X12) = (X13)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.51  thf(t65_zfmisc_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.19/0.51       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X14 : $i, X15 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X14 @ X15)
% 0.19/0.51          | ((k4_xboole_0 @ X15 @ (k1_tarski @ X14)) != (X15)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.19/0.51          | ((X0) = (X1))
% 0.19/0.51          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((((sk_C) = (sk_A)))
% 0.19/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '10'])).
% 0.19/0.51  thf('12', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      ((((sk_A) != (sk_A)))
% 0.19/0.51         <= (~ (((sk_A) = (sk_C))) & 
% 0.19/0.51             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      ((((sk_A) = (sk_C))) | 
% 0.19/0.51       ~
% 0.19/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.19/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.51      inference('split', [status(esa)], ['3'])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      ((((sk_C) = (sk_A)))
% 0.19/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '10'])).
% 0.19/0.51  thf(t69_enumset1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.51  thf('17', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51         (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ sk_D)))
% 0.19/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.51      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.51         ((r2_hidden @ X8 @ X9)
% 0.19/0.51          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.19/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (((r2_hidden @ sk_B @ sk_D))
% 0.19/0.51         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.19/0.51       ~
% 0.19/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (~
% 0.19/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['2', '14', '22'])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51          (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.19/0.51  thf('25', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.19/0.51      inference('split', [status(esa)], ['3'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      ((((sk_A) = (sk_C))) | 
% 0.19/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.51      inference('split', [status(esa)], ['3'])).
% 0.19/0.51  thf('27', plain, ((((sk_A) = (sk_C)))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['2', '14', '22', '26'])).
% 0.19/0.51  thf('28', plain, (((sk_A) = (sk_C))),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.19/0.51  thf('29', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51          (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ sk_D))),
% 0.19/0.51      inference('demod', [status(thm)], ['24', '28', '29'])).
% 0.19/0.51  thf('31', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (![X15 : $i, X16 : $i]:
% 0.19/0.51         (((k4_xboole_0 @ X15 @ (k1_tarski @ X16)) = (X15))
% 0.19/0.51          | (r2_hidden @ X16 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i]:
% 0.19/0.51         (((X12) != (X11))
% 0.19/0.51          | ((k4_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X11))
% 0.19/0.51              != (k1_tarski @ X12)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X11 : $i]:
% 0.19/0.51         ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X11))
% 0.19/0.51           != (k1_tarski @ X11))),
% 0.19/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.19/0.51          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['32', '34'])).
% 0.19/0.51  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.19/0.51  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['31', '36'])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (((r2_hidden @ sk_B @ sk_D)
% 0.19/0.51        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.19/0.51      inference('split', [status(esa)], ['38'])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.19/0.51       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.19/0.51         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.19/0.51      inference('split', [status(esa)], ['38'])).
% 0.19/0.51  thf('41', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['2', '14', '22', '40'])).
% 0.19/0.51  thf('42', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['39', '41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.19/0.51         ((r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X10))
% 0.19/0.51          | ~ (r2_hidden @ X8 @ X10)
% 0.19/0.51          | ~ (r2_hidden @ X6 @ X7))),
% 0.19/0.51      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.51          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.51  thf('45', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.19/0.51          (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ sk_D))),
% 0.19/0.51      inference('sup-', [status(thm)], ['37', '44'])).
% 0.19/0.51  thf('46', plain, ($false), inference('demod', [status(thm)], ['30', '45'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
