%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.27ElfpPPR9

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 139 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  406 (1520 expanded)
%              Number of equality atoms :   26 ( 100 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X9 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','10'])).

thf('12',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','11'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( r1_xboole_0 @ ( k2_tarski @ X12 @ X14 ) @ X13 )
      | ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X9 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('25',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','10','23','24'])).

thf('26',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['16','25'])).

thf('27',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','10','23','24','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['28','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['12','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.27ElfpPPR9
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:48:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 67 iterations in 0.015s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(t72_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.49       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.49          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_A @ sk_C)
% 0.21/0.49        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49            = (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.49       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49          = (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ sk_C)
% 0.21/0.49        | (r2_hidden @ sk_A @ sk_C)
% 0.21/0.49        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49            != (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49          = (k2_tarski @ sk_A @ sk_B)))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49                = (k2_tarski @ sk_A @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['0'])).
% 0.21/0.49  thf(t79_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49                = (k2_tarski @ sk_A @ sk_B))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t55_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k2_tarski @ X9 @ X10) @ X11)
% 0.21/0.49          | ~ (r2_hidden @ X9 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_A @ sk_C))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49                = (k2_tarski @ sk_A @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.21/0.49       ~
% 0.21/0.49       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49          = (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '9'])).
% 0.21/0.49  thf('11', plain, (~ ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['2', '10'])).
% 0.21/0.49  thf('12', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['1', '11'])).
% 0.21/0.49  thf(t57_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.21/0.49          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         ((r2_hidden @ X12 @ X13)
% 0.21/0.49          | (r1_xboole_0 @ (k2_tarski @ X12 @ X14) @ X13)
% 0.21/0.49          | (r2_hidden @ X14 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.21/0.49  thf(t83_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r2_hidden @ X1 @ X0)
% 0.21/0.49          | (r2_hidden @ X2 @ X0)
% 0.21/0.49          | ((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k2_tarski @ X2 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49          != (k2_tarski @ sk_A @ sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49                = (k2_tarski @ sk_A @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49                = (k2_tarski @ sk_A @ sk_B))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(commutativity_k2_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k2_tarski @ X9 @ X10) @ X11)
% 0.21/0.49          | ~ (r2_hidden @ X9 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_B @ sk_C))
% 0.21/0.49         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49                = (k2_tarski @ sk_A @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 0.21/0.49       ~
% 0.21/0.49       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49          = (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (~
% 0.21/0.49       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49          = (k2_tarski @ sk_A @ sk_B))) | 
% 0.21/0.49       ((r2_hidden @ sk_B @ sk_C)) | ((r2_hidden @ sk_A @ sk_C))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (~
% 0.21/0.49       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49          = (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['2', '10', '23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['16', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.21/0.49        | (r2_hidden @ sk_A @ sk_C)
% 0.21/0.49        | (r2_hidden @ sk_B @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '26'])).
% 0.21/0.49  thf('28', plain, (((r2_hidden @ sk_B @ sk_C) | (r2_hidden @ sk_A @ sk_C))),
% 0.21/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.21/0.49        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49            = (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 0.21/0.49       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.21/0.49          = (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['29'])).
% 0.21/0.49  thf('32', plain, (~ ((r2_hidden @ sk_B @ sk_C))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['2', '10', '23', '24', '31'])).
% 0.21/0.49  thf('33', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['30', '32'])).
% 0.21/0.49  thf('34', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.49      inference('clc', [status(thm)], ['28', '33'])).
% 0.21/0.49  thf('35', plain, ($false), inference('demod', [status(thm)], ['12', '34'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
