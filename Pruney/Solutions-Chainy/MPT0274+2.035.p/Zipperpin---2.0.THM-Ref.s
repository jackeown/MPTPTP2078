%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H1hUiaz9bt

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 153 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  458 (1721 expanded)
%              Number of equality atoms :   31 ( 121 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X14 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('9',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X14 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','13'])).

thf('15',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','14'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('16',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ X44 @ X45 )
      | ( r1_xboole_0 @ ( k2_tarski @ X44 @ X46 ) @ X45 )
      | ( r2_hidden @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k2_tarski @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X11: $i,X14: $i] :
      ( r2_hidden @ X11 @ ( k2_tarski @ X14 @ X11 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','13','27','28'])).

thf('30',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['19','29'])).

thf('31',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','13','27','28','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf('38',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(clc,[status(thm)],['32','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['15','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H1hUiaz9bt
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 103 iterations in 0.052s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(t72_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.51       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.51          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ sk_C_1)
% 0.20/0.51        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51            = (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.20/0.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51          = (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_C_1)
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_C_1)
% 0.20/0.51        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51            != (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51          = (k2_tarski @ sk_A @ sk_B)))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51                = (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(t79_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X7)),
% 0.20/0.51      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51                = (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf(d2_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (((X12) != (X14))
% 0.20/0.51          | (r2_hidden @ X12 @ X13)
% 0.20/0.51          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X11 : $i, X14 : $i]: (r2_hidden @ X14 @ (k2_tarski @ X14 @ X11))),
% 0.20/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.51  thf(t3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X2 @ X3)
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.51          | ~ (r2_hidden @ X1 @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ sk_C_1))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51                = (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.20/0.51       ~
% 0.20/0.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51          = (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '12'])).
% 0.20/0.51  thf('14', plain, (~ ((r2_hidden @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '13'])).
% 0.20/0.51  thf('15', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['1', '14'])).
% 0.20/0.51  thf(t57_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.20/0.51          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.51         ((r2_hidden @ X44 @ X45)
% 0.20/0.51          | (r1_xboole_0 @ (k2_tarski @ X44 @ X46) @ X45)
% 0.20/0.51          | (r2_hidden @ X46 @ X45))),
% 0.20/0.51      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.20/0.51  thf(t83_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0)
% 0.20/0.51          | (r2_hidden @ X2 @ X0)
% 0.20/0.51          | ((k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k2_tarski @ X2 @ X1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51          != (k2_tarski @ sk_A @ sk_B)))
% 0.20/0.51         <= (~
% 0.20/0.51             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51                = (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51                = (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (((X12) != (X11))
% 0.20/0.51          | (r2_hidden @ X12 @ X13)
% 0.20/0.51          | ((X13) != (k2_tarski @ X14 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X11 : $i, X14 : $i]: (r2_hidden @ X11 @ (k2_tarski @ X14 @ X11))),
% 0.20/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ X0)
% 0.20/0.51          | ~ (r2_hidden @ X2 @ X3)
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_C_1))
% 0.20/0.51         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51                = (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.20/0.51       ~
% 0.20/0.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51          = (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51          = (k2_tarski @ sk_A @ sk_B))) | 
% 0.20/0.51       ((r2_hidden @ sk_B @ sk_C_1)) | ((r2_hidden @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('split', [status(esa)], ['3'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (~
% 0.20/0.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51          = (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '13', '27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51         != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['19', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_A @ sk_C_1)
% 0.20/0.51        | (r2_hidden @ sk_B @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_C_1) | (r2_hidden @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 0.20/0.51        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51            = (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.20/0.51       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.51          = (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['33'])).
% 0.20/0.51  thf('36', plain, (~ ((r2_hidden @ sk_B @ sk_C_1))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '13', '27', '28', '35'])).
% 0.20/0.51  thf('37', plain, (~ (r2_hidden @ sk_B @ sk_C_1)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 0.20/0.51  thf('38', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.20/0.51      inference('clc', [status(thm)], ['32', '37'])).
% 0.20/0.51  thf('39', plain, ($false), inference('demod', [status(thm)], ['15', '38'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
