%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6XS4Yc4X53

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 165 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  477 (1770 expanded)
%              Number of equality atoms :   31 ( 115 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B != sk_D )
    | ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
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
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) )
        = ( k1_tarski @ X12 ) )
      | ( X12 = X13 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X21 )
      | ~ ( r2_hidden @ X19 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ~ ( r2_hidden @ X21 @ ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( sk_D = sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B = sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','8','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','22'])).

thf('24',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('27',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','8','21','26'])).

thf('28',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','8','21','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simpl_trail,[status(thm)],['30','32'])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X18 ) ) )
      | ( X16 != X18 )
      | ( X15 != X14 ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('35',plain,(
    ! [X14: $i,X18: $i] :
      ( r2_hidden @ ( k4_tarski @ X14 @ X18 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('37',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X10 ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['29','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6XS4Yc4X53
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:55:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 154 iterations in 0.057s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(t129_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( r2_hidden @
% 0.20/0.50         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.50       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50        ( ( r2_hidden @
% 0.20/0.50            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.50          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((((sk_B) != (sk_D))
% 0.20/0.50        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.20/0.50        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (~
% 0.20/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))) | 
% 0.20/0.50       ~ (((sk_B) = (sk_D))) | ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((r2_hidden @ sk_A @ sk_C)
% 0.20/0.50        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf(l54_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         ((r2_hidden @ X6 @ X7)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (((r2_hidden @ sk_A @ sk_C))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.20/0.50       ~
% 0.20/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         ((r2_hidden @ X8 @ X9)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('12', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(t20_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.50         ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ( A ) != ( B ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13))
% 0.20/0.50            = (k1_tarski @ X12))
% 0.20/0.50          | ((X12) = (X13)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1))
% 0.20/0.50            = (k1_tarski @ X0))
% 0.20/0.50          | ((X0) = (X1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf(t64_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.50       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.50         (((X19) != (X21))
% 0.20/0.50          | ~ (r2_hidden @ X19 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X21))))),
% 0.20/0.50      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         ~ (r2_hidden @ X21 @ (k4_xboole_0 @ X20 @ (k1_tarski @ X21)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((((sk_D) = (sk_B)))
% 0.20/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '17'])).
% 0.20/0.50  thf('19', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((((sk_B) != (sk_B)))
% 0.20/0.50         <= (~ (((sk_B) = (sk_D))) & 
% 0.20/0.50             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50               (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((((sk_B) = (sk_D))) | 
% 0.20/0.50       ~
% 0.20/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (~
% 0.20/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '8', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D)))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['1', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((((sk_B) = (sk_D))
% 0.20/0.50        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50           (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((((sk_B) = (sk_D))) | 
% 0.20/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['24'])).
% 0.20/0.50  thf('27', plain, ((((sk_B) = (sk_D)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '8', '21', '26'])).
% 0.20/0.50  thf('28', plain, (((sk_B) = (sk_D))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.20/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.50         (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('32', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['2', '8', '21', '31'])).
% 0.20/0.50  thf('33', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['30', '32'])).
% 0.20/0.50  thf(t34_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( r2_hidden @
% 0.20/0.50         ( k4_tarski @ A @ B ) @ 
% 0.20/0.50         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.20/0.50         ((r2_hidden @ (k4_tarski @ X15 @ X16) @ 
% 0.20/0.50           (k2_zfmisc_1 @ (k1_tarski @ X14) @ (k1_tarski @ X18)))
% 0.20/0.50          | ((X16) != (X18))
% 0.20/0.50          | ((X15) != (X14)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X14 : $i, X18 : $i]:
% 0.20/0.50         (r2_hidden @ (k4_tarski @ X14 @ X18) @ 
% 0.20/0.50          (k2_zfmisc_1 @ (k1_tarski @ X14) @ (k1_tarski @ X18)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         ((r2_hidden @ X6 @ X7)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.50  thf('37', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.50         ((r2_hidden @ (k4_tarski @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X10))
% 0.20/0.50          | ~ (r2_hidden @ X8 @ X10)
% 0.20/0.50          | ~ (r2_hidden @ X6 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X2 @ X1)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.20/0.50             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.20/0.50          (k2_zfmisc_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '39'])).
% 0.20/0.50  thf('41', plain, ($false), inference('demod', [status(thm)], ['29', '40'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
