%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tX5xrbaChZ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 233 expanded)
%              Number of leaves         :   17 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  545 (2508 expanded)
%              Number of equality atoms :   43 ( 221 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B != sk_D )
    | ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
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
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X18 ) )
      | ( X17 = X18 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('22',plain,
    ( ( sk_B = sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_B = sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','13','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    sk_A = sk_C ),
    inference('sat_resolution*',[status(thm)],['2','13','25','29'])).

thf('31',plain,(
    sk_A = sk_C ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['14'])).

thf('34',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['14'])).

thf('35',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','13','25','34'])).

thf('36',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','31','32','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('41',plain,(
    ! [X16: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['37','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tX5xrbaChZ
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:56:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 84 iterations in 0.025s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(t34_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @
% 0.21/0.48         ( k4_tarski @ A @ B ) @ 
% 0.21/0.48         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( r2_hidden @
% 0.21/0.48            ( k4_tarski @ A @ B ) @ 
% 0.21/0.48            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.48          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((sk_B) != (sk_D))
% 0.21/0.48        | ((sk_A) != (sk_C))
% 0.21/0.48        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.21/0.48       ~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((((sk_A) = (sk_C))
% 0.21/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf(l54_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         ((r2_hidden @ X10 @ X11)
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf(t17_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) != ( B ) ) =>
% 0.21/0.48       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k1_tarski @ X17) @ (k1_tarski @ X18))
% 0.21/0.48          | ((X17) = (X18)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.48  thf(l24_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ (k1_tarski @ X6) @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((((sk_A) = (sk_C)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.48  thf('11', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((((sk_A) != (sk_A)))
% 0.21/0.48         <= (~ (((sk_A) = (sk_C))) & 
% 0.21/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((((sk_A) = (sk_C))) | 
% 0.21/0.48       ~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((sk_B) = (sk_D))
% 0.21/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('split', [status(esa)], ['14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((sk_A) = (sk_C)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('17', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ (k1_tarski @ sk_D))))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         ((r2_hidden @ X12 @ X13)
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((((sk_B) = (sk_D)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((((sk_B) != (sk_B)))
% 0.21/0.48         <= (~ (((sk_B) = (sk_D))) & 
% 0.21/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((((sk_B) = (sk_D))) | 
% 0.21/0.48       ~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '13', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48          (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.21/0.48  thf('28', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((((sk_A) = (sk_C))) | 
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['3'])).
% 0.21/0.48  thf('30', plain, ((((sk_A) = (sk_C)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '13', '25', '29'])).
% 0.21/0.48  thf('31', plain, (((sk_A) = (sk_C))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.21/0.48  thf('32', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('33', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['14'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((((sk_B) = (sk_D))) | 
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['14'])).
% 0.21/0.48  thf('35', plain, ((((sk_B) = (sk_D)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '13', '25', '34'])).
% 0.21/0.48  thf('36', plain, (((sk_B) = (sk_D))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48          (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '31', '32', '36'])).
% 0.21/0.48  thf('38', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(l27_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k1_tarski @ X8) @ X9) | (r2_hidden @ X8 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.48  thf(t16_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.21/0.48          ( ( A ) = ( B ) ) ) ))).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16))
% 0.21/0.48          | ((X15) != (X16)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X16 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X16))),
% 0.21/0.48      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.48  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['39', '41'])).
% 0.21/0.48  thf('43', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['38', '42'])).
% 0.21/0.48  thf('44', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['39', '41'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 0.21/0.48          | ~ (r2_hidden @ X12 @ X14)
% 0.21/0.48          | ~ (r2_hidden @ X10 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X1)
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.21/0.48             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.21/0.48          (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['43', '46'])).
% 0.21/0.48  thf('48', plain, ($false), inference('demod', [status(thm)], ['37', '47'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
