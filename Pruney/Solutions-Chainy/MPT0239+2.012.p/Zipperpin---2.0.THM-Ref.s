%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lsEiiovTKf

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 217 expanded)
%              Number of leaves         :   15 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  602 (2517 expanded)
%              Number of equality atoms :   59 ( 281 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) )
        = ( k1_tarski @ X15 ) )
      | ( X15 = X16 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
       != ( k1_tarski @ X6 ) ) ) ),
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
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_tarski @ sk_D ) ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
      & ( sk_A = sk_C ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('23',plain,
    ( ( sk_B = sk_D )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_A != sk_C )
    | ( sk_B = sk_D ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','14','26'])).

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
    inference('sat_resolution*',[status(thm)],['2','14','26','30'])).

thf('32',plain,(
    sk_A = sk_C ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('37',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','14','26','36'])).

thf('38',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','32','33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X8 )
        = ( k1_tarski @ X6 ) )
      | ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 != X14 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X14 ) )
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('43',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X14 ) )
     != ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ ( k2_zfmisc_1 @ X10 @ X13 ) )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['39','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lsEiiovTKf
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 90 iterations in 0.036s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(t34_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( r2_hidden @
% 0.21/0.49         ( k4_tarski @ A @ B ) @ 
% 0.21/0.49         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.49       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49        ( ( r2_hidden @
% 0.21/0.49            ( k4_tarski @ A @ B ) @ 
% 0.21/0.49            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.49          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((((sk_B) != (sk_D))
% 0.21/0.49        | ((sk_A) != (sk_C))
% 0.21/0.49        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.21/0.49       ~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((((sk_A) = (sk_C))
% 0.21/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf(l54_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         ((r2_hidden @ X9 @ X10)
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf(t20_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.49         ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ( A ) != ( B ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16))
% 0.21/0.49            = (k1_tarski @ X15))
% 0.21/0.49          | ((X15) = (X16)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.49  thf(l33_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.49          | ((k4_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_tarski @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((((sk_A) = (sk_C)))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '10'])).
% 0.21/0.49  thf('12', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((((sk_A) != (sk_A)))
% 0.21/0.49         <= (~ (((sk_A) = (sk_C))) & 
% 0.21/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((((sk_A) = (sk_C))) | 
% 0.21/0.49       ~
% 0.21/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) & 
% 0.21/0.49             (((sk_A) = (sk_C))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('18', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ (k1_tarski @ sk_D))))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) & 
% 0.21/0.49             (((sk_A) = (sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         ((r2_hidden @ X11 @ X12)
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) & 
% 0.21/0.49             (((sk_A) = (sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((sk_B) = (sk_D)))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) & 
% 0.21/0.49             (((sk_A) = (sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((((sk_B) != (sk_B)))
% 0.21/0.49         <= (~ (((sk_B) = (sk_D))) & 
% 0.21/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) & 
% 0.21/0.49             (((sk_A) = (sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.21/0.49       ~ (((sk_A) = (sk_C))) | (((sk_B) = (sk_D)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['2', '14', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.21/0.49  thf('29', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((((sk_A) = (sk_C))) | 
% 0.21/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('31', plain, ((((sk_A) = (sk_C)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['2', '14', '26', '30'])).
% 0.21/0.49  thf('32', plain, (((sk_A) = (sk_C))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['29', '31'])).
% 0.21/0.49  thf('33', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((((sk_B) = (sk_D))
% 0.21/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((((sk_B) = (sk_D))) | 
% 0.21/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.21/0.49      inference('split', [status(esa)], ['34'])).
% 0.21/0.49  thf('37', plain, ((((sk_B) = (sk_D)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['2', '14', '26', '36'])).
% 0.21/0.49  thf('38', plain, (((sk_B) = (sk_D))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49          (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['28', '32', '33', '38'])).
% 0.21/0.49  thf('40', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X6 : $i, X8 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ (k1_tarski @ X6) @ X8) = (k1_tarski @ X6))
% 0.21/0.49          | (r2_hidden @ X6 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i]:
% 0.21/0.49         (((X15) != (X14))
% 0.21/0.49          | ((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X14))
% 0.21/0.49              != (k1_tarski @ X15)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X14 : $i]:
% 0.21/0.49         ((k4_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X14))
% 0.21/0.49           != (k1_tarski @ X14))),
% 0.21/0.49      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.49          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['41', '43'])).
% 0.21/0.49  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.49  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['40', '45'])).
% 0.21/0.49  thf('47', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 0.21/0.49         ((r2_hidden @ (k4_tarski @ X9 @ X11) @ (k2_zfmisc_1 @ X10 @ X13))
% 0.21/0.49          | ~ (r2_hidden @ X11 @ X13)
% 0.21/0.49          | ~ (r2_hidden @ X9 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X2 @ X1)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.21/0.49             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.21/0.49          (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.49  thf('51', plain, ($false), inference('demod', [status(thm)], ['39', '50'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
