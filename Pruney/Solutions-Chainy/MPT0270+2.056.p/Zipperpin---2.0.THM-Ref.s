%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wk93DGhoxy

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  70 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 ( 586 expanded)
%              Number of equality atoms :   22 (  56 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('14',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X43 ) @ X44 )
      | ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','11','18'])).

thf('20',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['17','19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['13','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wk93DGhoxy
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:26:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 76 iterations in 0.035s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(t67_zfmisc_1, conjecture,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.54       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i]:
% 0.22/0.54        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.54          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.22/0.54        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('split', [status(esa)], ['0'])).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.22/0.54       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['0'])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (((r2_hidden @ sk_A @ sk_B_1)
% 0.22/0.54        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('split', [status(esa)], ['3'])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.22/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['0'])).
% 0.22/0.54  thf(t83_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X10 : $i, X12 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 0.22/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.22/0.54         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.22/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.22/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.54  thf(l24_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X41 : $i, X42 : $i]:
% 0.22/0.54         (~ (r1_xboole_0 @ (k1_tarski @ X41) @ X42) | ~ (r2_hidden @ X41 @ X42))),
% 0.22/0.54      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((~ (r2_hidden @ sk_A @ sk_B_1))
% 0.22/0.54         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.22/0.54       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '10'])).
% 0.22/0.54  thf('12', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['2', '11'])).
% 0.22/0.54  thf('13', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.22/0.54  thf(l27_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X43 : $i, X44 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ (k1_tarski @ X43) @ X44) | (r2_hidden @ X43 @ X44))),
% 0.22/0.54      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r2_hidden @ X1 @ X0)
% 0.22/0.54          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.22/0.54         <= (~
% 0.22/0.54             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['3'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.22/0.54       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.22/0.54      inference('split', [status(esa)], ['3'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['2', '11', '18'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A))),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['17', '19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.22/0.54        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '20'])).
% 0.22/0.54  thf('22', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.22/0.54      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.54  thf('23', plain, ($false), inference('demod', [status(thm)], ['13', '22'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
