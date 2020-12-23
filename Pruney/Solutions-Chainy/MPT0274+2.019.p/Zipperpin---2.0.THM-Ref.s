%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zVnSTxUfN3

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 144 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  437 (1655 expanded)
%              Number of equality atoms :   30 ( 120 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k4_xboole_0 @ X2 @ X4 )
       != X2 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,
    ( ( ( ( k2_tarski @ sk_A @ sk_B )
       != ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ( r1_xboole_0 @ ( k2_tarski @ X31 @ X33 ) @ X32 )
      | ( r2_hidden @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('27',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','12','25','26'])).

thf('28',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['18','27'])).

thf('29',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['31'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['3','12','25','26','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['30','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['14','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zVnSTxUfN3
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 95 iterations in 0.038s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(t72_zfmisc_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.50       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.50        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.50          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_A @ sk_C)
% 0.19/0.50        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50            = (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.19/0.50      inference('split', [status(esa)], ['0'])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_A @ sk_C)
% 0.19/0.50        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50            = (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.19/0.50       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50          = (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('split', [status(esa)], ['2'])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (((r2_hidden @ sk_B @ sk_C)
% 0.19/0.50        | (r2_hidden @ sk_A @ sk_C)
% 0.19/0.50        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50            != (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.19/0.50      inference('split', [status(esa)], ['4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50          = (k2_tarski @ sk_A @ sk_B)))
% 0.19/0.50         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50                = (k2_tarski @ sk_A @ sk_B))))),
% 0.19/0.50      inference('split', [status(esa)], ['2'])).
% 0.19/0.50  thf(t83_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X2 : $i, X4 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X2 @ X4) | ((k4_xboole_0 @ X2 @ X4) != (X2)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.19/0.50         | (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 0.19/0.50         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50                = (k2_tarski @ sk_A @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.19/0.50         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50                = (k2_tarski @ sk_A @ sk_B))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.50  thf(t55_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ (k2_tarski @ X28 @ X29) @ X30)
% 0.19/0.50          | ~ (r2_hidden @ X28 @ X30))),
% 0.19/0.50      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_A @ sk_C))
% 0.19/0.50         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50                = (k2_tarski @ sk_A @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.19/0.50       ~
% 0.19/0.50       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50          = (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '11'])).
% 0.19/0.50  thf('13', plain, (~ ((r2_hidden @ sk_A @ sk_C))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['3', '12'])).
% 0.19/0.50  thf('14', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.19/0.50  thf(t57_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.19/0.50          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.50         ((r2_hidden @ X31 @ X32)
% 0.19/0.50          | (r1_xboole_0 @ (k2_tarski @ X31 @ X33) @ X32)
% 0.19/0.50          | (r2_hidden @ X33 @ X32))),
% 0.19/0.50      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]:
% 0.19/0.50         (((k4_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_hidden @ X1 @ X0)
% 0.19/0.50          | (r2_hidden @ X2 @ X0)
% 0.19/0.50          | ((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k2_tarski @ X2 @ X1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50          != (k2_tarski @ sk_A @ sk_B)))
% 0.19/0.50         <= (~
% 0.19/0.50             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50                = (k2_tarski @ sk_A @ sk_B))))),
% 0.19/0.50      inference('split', [status(esa)], ['4'])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.19/0.50      inference('split', [status(esa)], ['4'])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.19/0.50         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50                = (k2_tarski @ sk_A @ sk_B))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.50  thf(commutativity_k2_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i]:
% 0.19/0.50         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.19/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ (k2_tarski @ X28 @ X29) @ X30)
% 0.19/0.50          | ~ (r2_hidden @ X28 @ X30))),
% 0.19/0.50      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.19/0.50          | ~ (r2_hidden @ X0 @ X2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_B @ sk_C))
% 0.19/0.50         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50                = (k2_tarski @ sk_A @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '23'])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 0.19/0.50       ~
% 0.19/0.50       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50          = (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['19', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (~
% 0.19/0.50       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50          = (k2_tarski @ sk_A @ sk_B))) | 
% 0.19/0.50       ((r2_hidden @ sk_B @ sk_C)) | ((r2_hidden @ sk_A @ sk_C))),
% 0.19/0.50      inference('split', [status(esa)], ['4'])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (~
% 0.19/0.50       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50          = (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['3', '12', '25', '26'])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['18', '27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.19/0.50        | (r2_hidden @ sk_A @ sk_C)
% 0.19/0.50        | (r2_hidden @ sk_B @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['17', '28'])).
% 0.19/0.50  thf('30', plain, (((r2_hidden @ sk_B @ sk_C) | (r2_hidden @ sk_A @ sk_C))),
% 0.19/0.50      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.19/0.50        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50            = (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.19/0.50      inference('split', [status(esa)], ['31'])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 0.19/0.50       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.19/0.50          = (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('split', [status(esa)], ['31'])).
% 0.19/0.50  thf('34', plain, (~ ((r2_hidden @ sk_B @ sk_C))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['3', '12', '25', '26', '33'])).
% 0.19/0.50  thf('35', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.19/0.50  thf('36', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.19/0.50      inference('clc', [status(thm)], ['30', '35'])).
% 0.19/0.50  thf('37', plain, ($false), inference('demod', [status(thm)], ['14', '36'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
