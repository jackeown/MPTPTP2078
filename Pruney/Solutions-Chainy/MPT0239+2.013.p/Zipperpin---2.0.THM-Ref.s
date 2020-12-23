%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1pCFxdr4wi

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 268 expanded)
%              Number of leaves         :   15 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  600 (3058 expanded)
%              Number of equality atoms :   56 ( 325 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
        = ( k1_tarski @ X16 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X6 @ X8 ) @ X7 )
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('18',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('23',plain,
    ( ( sk_B = sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','16','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('29',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,(
    sk_A = sk_C ),
    inference('sat_resolution*',[status(thm)],['2','16','26','30'])).

thf('32',plain,(
    sk_A = sk_C ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf('33',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('36',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','16','26','35'])).

thf('37',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf('38',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','32','37'])).

thf('39',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X6 @ X8 ) @ X9 )
        = ( k1_tarski @ X6 ) )
      | ( X6 != X8 )
      | ( r2_hidden @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X8 @ X8 ) @ X9 )
        = ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 != X15 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X15 ) )
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('43',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X15 ) )
     != ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['38','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1pCFxdr4wi
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 85 iterations in 0.035s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(t34_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( r2_hidden @
% 0.21/0.47         ( k4_tarski @ A @ B ) @ 
% 0.21/0.47         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.47       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47        ( ( r2_hidden @
% 0.21/0.47            ( k4_tarski @ A @ B ) @ 
% 0.21/0.47            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.47          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((sk_B) != (sk_D))
% 0.21/0.47        | ((sk_A) != (sk_C))
% 0.21/0.47        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.21/0.47         <= (~
% 0.21/0.47             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (~
% 0.21/0.47       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.21/0.47       ~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((((sk_A) = (sk_C))
% 0.21/0.47        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.21/0.47         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf(l54_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.47       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.47         ((r2_hidden @ X10 @ X11)
% 0.21/0.47          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.21/0.47         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(t20_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.47         ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ( A ) != ( B ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X16 : $i, X17 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 0.21/0.47            = (k1_tarski @ X16))
% 0.21/0.47          | ((X16) = (X17)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.47  thf(t69_enumset1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.47  thf('8', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.47  thf(l38_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.47         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.47          | ((k4_xboole_0 @ (k2_tarski @ X6 @ X8) @ X7) != (k1_tarski @ X6)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.47          | ((X0) = (X1))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((((sk_A) = (sk_C)))
% 0.21/0.47         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '12'])).
% 0.21/0.47  thf('14', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((((sk_A) != (sk_A)))
% 0.21/0.47         <= (~ (((sk_A) = (sk_C))) & 
% 0.21/0.47             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((((sk_A) = (sk_C))) | 
% 0.21/0.47       ~
% 0.21/0.47       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.21/0.47         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((((sk_A) = (sk_C)))
% 0.21/0.47         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '12'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))))
% 0.21/0.47         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.47         ((r2_hidden @ X12 @ X13)
% 0.21/0.47          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.21/0.47         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((((sk_B) = (sk_D)))
% 0.21/0.47         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((((sk_B) != (sk_B)))
% 0.21/0.47         <= (~ (((sk_B) = (sk_D))) & 
% 0.21/0.47             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      ((((sk_B) = (sk_D))) | 
% 0.21/0.47       ~
% 0.21/0.47       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (~
% 0.21/0.47       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['2', '16', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47          (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.21/0.47  thf('29', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      ((((sk_A) = (sk_C))) | 
% 0.21/0.47       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.47      inference('split', [status(esa)], ['3'])).
% 0.21/0.47  thf('31', plain, ((((sk_A) = (sk_C)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['2', '16', '26', '30'])).
% 0.21/0.47  thf('32', plain, (((sk_A) = (sk_C))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['29', '31'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      ((((sk_B) = (sk_D))
% 0.21/0.47        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.47           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('34', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.21/0.47      inference('split', [status(esa)], ['33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((((sk_B) = (sk_D))) | 
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.48      inference('split', [status(esa)], ['33'])).
% 0.21/0.48  thf('36', plain, ((((sk_B) = (sk_D)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '16', '26', '35'])).
% 0.21/0.48  thf('37', plain, (((sk_B) = (sk_D))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['28', '32', '37'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ (k2_tarski @ X6 @ X8) @ X9) = (k1_tarski @ X6))
% 0.21/0.48          | ((X6) != (X8))
% 0.21/0.48          | (r2_hidden @ X6 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         ((r2_hidden @ X8 @ X9)
% 0.21/0.48          | ((k4_xboole_0 @ (k2_tarski @ X8 @ X8) @ X9) = (k1_tarski @ X8)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.48  thf('41', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i]:
% 0.21/0.48         (((X16) != (X15))
% 0.21/0.48          | ((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X15))
% 0.21/0.48              != (k1_tarski @ X16)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X15 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X15))
% 0.21/0.48           != (k1_tarski @ X15))),
% 0.21/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.21/0.48           != (k1_tarski @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['41', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.48          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '44'])).
% 0.21/0.48  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.48  thf('47', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X14))
% 0.21/0.48          | ~ (r2_hidden @ X12 @ X14)
% 0.21/0.48          | ~ (r2_hidden @ X10 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X1)
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.21/0.48             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.21/0.48          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.48  thf('51', plain, ($false), inference('demod', [status(thm)], ['38', '50'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
