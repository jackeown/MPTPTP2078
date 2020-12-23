%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ppLBh0snfN

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  84 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  507 ( 871 expanded)
%              Number of equality atoms :   37 (  61 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t69_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ X16 )
        = ( k1_tarski @ X15 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ X16 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t69_zfmisc_1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
      = k1_xboole_0 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(t21_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 = X13 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X13 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t21_zfmisc_1])).

thf('11',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( ( k3_xboole_0 @ X4 @ ( k1_tarski @ X3 ) )
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X12 ) )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_A != sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['22'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','16','17','30','31','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ppLBh0snfN
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 136 iterations in 0.064s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(t128_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( r2_hidden @
% 0.20/0.52         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.52       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52        ( ( r2_hidden @
% 0.20/0.52            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.52          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((((sk_A) = (sk_C))
% 0.20/0.52        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((((sk_A) = (sk_C))) | 
% 0.20/0.52       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf(l54_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         ((r2_hidden @ X8 @ X9)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf(t69_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.20/0.52       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ (k1_tarski @ X15) @ X16) = (k1_tarski @ X15))
% 0.20/0.52          | ((k4_xboole_0 @ (k1_tarski @ X15) @ X16) = (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_zfmisc_1])).
% 0.20/0.52  thf(l33_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.52       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.52          | ((k4_xboole_0 @ (k1_tarski @ X5) @ X6) != (k1_tarski @ X5)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.52          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.20/0.52          = (k1_xboole_0)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '8'])).
% 0.20/0.52  thf(t21_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.52         ( k1_xboole_0 ) ) =>
% 0.20/0.52       ( ( A ) = ( B ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (((X14) = (X13))
% 0.20/0.52          | ((k4_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X13))
% 0.20/0.52              != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t21_zfmisc_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (sk_C))))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      ((((sk_A) = (sk_C)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.20/0.52        | ((sk_A) != (sk_C))
% 0.20/0.52        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      ((((sk_A) != (sk_A)))
% 0.20/0.52         <= (~ (((sk_A) = (sk_C))) & 
% 0.20/0.52             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((((sk_A) = (sk_C))) | 
% 0.20/0.52       ~
% 0.20/0.52       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (~ (((sk_A) = (sk_C))) | 
% 0.20/0.52       ~
% 0.20/0.52       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['13'])).
% 0.20/0.52  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.52  thf('18', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.52  thf(l29_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.20/0.52       ( r2_hidden @ B @ A ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         ((r2_hidden @ X3 @ X4)
% 0.20/0.52          | ((k3_xboole_0 @ X4 @ (k1_tarski @ X3)) != (k1_tarski @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.52          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ sk_D)
% 0.20/0.52        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.52         ((r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X12))
% 0.20/0.52          | ~ (r2_hidden @ X10 @ X12)
% 0.20/0.52          | ~ (r2_hidden @ X8 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((![X0 : $i, X1 : $i]:
% 0.20/0.52          (~ (r2_hidden @ X1 @ X0)
% 0.20/0.52           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.20/0.52         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.20/0.52           (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D)))
% 0.20/0.52         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '25'])).
% 0.20/0.52  thf('27', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.52      inference('split', [status(esa)], ['13'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) & 
% 0.20/0.52             (((sk_A) = (sk_C))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (~ (((sk_A) = (sk_C))) | 
% 0.20/0.52       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.52       ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.52      inference('split', [status(esa)], ['22'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         ((r2_hidden @ X10 @ X11)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ sk_D))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.52      inference('split', [status(esa)], ['13'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (~
% 0.20/0.52       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.52         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.52       ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)],
% 0.20/0.52                ['1', '16', '17', '30', '31', '36'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
