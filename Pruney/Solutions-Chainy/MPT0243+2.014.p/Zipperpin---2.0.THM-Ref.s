%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9b7EMgqAQ8

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 172 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  412 (1477 expanded)
%              Number of equality atoms :    8 (  23 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t38_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k1_tarski @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k2_tarski @ X14 @ X17 ) )
      | ( X16
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('15',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k1_tarski @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','12','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('28',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['25'])).

thf('30',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','12','22','29'])).

thf('31',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('34',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','12','22','35'])).

thf('37',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X8 @ X7 )
      | ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('42',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['24','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9b7EMgqAQ8
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 69 iterations in 0.027s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(t38_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.49          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.21/0.49        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.21/0.49        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.21/0.49         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.21/0.49       ~ ((r2_hidden @ sk_B @ sk_C)) | ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ sk_C)
% 0.21/0.49        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.21/0.49         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf(t41_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k2_tarski @ A @ B ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         ((k2_tarski @ X9 @ X10)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X9) @ (k1_tarski @ X10)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.49  thf(t11_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.49          | (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C))
% 0.21/0.49         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.49  thf(l1_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         ((r2_hidden @ X11 @ X12) | ~ (r1_tarski @ (k1_tarski @ X11) @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ sk_C))
% 0.21/0.49         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.49       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.21/0.49         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf(l45_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.49       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.49            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         ((r1_tarski @ X16 @ (k2_tarski @ X14 @ X17))
% 0.21/0.49          | ((X16) != (k1_tarski @ X17)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X14 : $i, X17 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_tarski @ X17) @ (k2_tarski @ X14 @ X17))),
% 0.21/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.49  thf(t1_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.49       ( r1_tarski @ A @ C ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.49          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.49          | (r1_tarski @ X3 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_tarski @ X0) @ X2)
% 0.21/0.49          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C))
% 0.21/0.49         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         ((r2_hidden @ X11 @ X12) | ~ (r1_tarski @ (k1_tarski @ X11) @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ sk_C))
% 0.21/0.49         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ sk_C)) | 
% 0.21/0.49       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['2', '12', '22'])).
% 0.21/0.49  thf('24', plain, (~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ sk_C)
% 0.21/0.49        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X11 : $i, X13 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C))
% 0.21/0.49         <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ sk_C)) | 
% 0.21/0.49       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('split', [status(esa)], ['25'])).
% 0.21/0.49  thf('30', plain, (((r2_hidden @ sk_B @ sk_C))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['2', '12', '22', '29'])).
% 0.21/0.49  thf('31', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_C)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X11 : $i, X13 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C))
% 0.21/0.49         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.49       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('36', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['2', '12', '22', '35'])).
% 0.21/0.49  thf('37', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 0.21/0.49  thf(t8_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.49       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.49          | ~ (r1_tarski @ X8 @ X7)
% 0.21/0.49          | (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ sk_C)
% 0.21/0.49          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.21/0.49        sk_C)),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         ((k2_tarski @ X9 @ X10)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X9) @ (k1_tarski @ X10)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.49  thf('42', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, ($false), inference('demod', [status(thm)], ['24', '42'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
