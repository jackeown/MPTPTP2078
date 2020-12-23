%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XExkqQocIL

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  82 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 ( 775 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t15_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ( X9
        = ( k4_xboole_0 @ X9 @ ( k2_tarski @ X8 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X11 @ X13 ) @ X12 )
       != ( k2_tarski @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ X2 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( sk_C_1
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('19',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('24',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['16','24'])).

thf('26',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('28',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('30',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('31',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['22','30'])).

thf('32',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['29','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XExkqQocIL
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:53:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 79 iterations in 0.044s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(t15_mcart_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.21/0.48       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.21/0.48          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.48            ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t15_mcart_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1) @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t10_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_mcart_1 @ X15) @ X16)
% 0.21/0.48          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t144_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.21/0.48          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.48         ((r2_hidden @ X8 @ X9)
% 0.21/0.48          | (r2_hidden @ X10 @ X9)
% 0.21/0.48          | ((X9) = (k4_xboole_0 @ X9 @ (k2_tarski @ X8 @ X10))))),
% 0.21/0.48      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('4', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(t72_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.48       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X11 @ X12)
% 0.21/0.48          | ((k4_xboole_0 @ (k2_tarski @ X11 @ X13) @ X12)
% 0.21/0.48              != (k2_tarski @ X11 @ X13)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k2_tarski @ X0 @ X0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.48          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.48          | (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.21/0.48          | ~ (r2_hidden @ X0 @ (k2_tarski @ X2 @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (k2_tarski @ X2 @ X1))
% 0.21/0.48          | (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.21/0.48          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((r2_hidden @ sk_C_1 @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.21/0.48        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '10'])).
% 0.21/0.48  thf(d1_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i, X3 : $i]:
% 0.21/0.48         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.21/0.48        | ((sk_C_1) = (k1_mcart_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((((k1_mcart_1 @ sk_A) != (sk_C_1))
% 0.21/0.48        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((((k1_mcart_1 @ sk_A) != (sk_C_1)))
% 0.21/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.21/0.48      inference('split', [status(esa)], ['15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1) @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.48         ((r2_hidden @ (k2_mcart_1 @ X15) @ X17)
% 0.21/0.48          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.48  thf('19', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D)),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.21/0.48        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))
% 0.21/0.48         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D)))),
% 0.21/0.48      inference('split', [status(esa)], ['20'])).
% 0.21/0.48  thf('22', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.21/0.48       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.21/0.48      inference('split', [status(esa)], ['15'])).
% 0.21/0.48  thf('24', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, (((k1_mcart_1 @ sk_A) != (sk_C_1))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['16', '24'])).
% 0.21/0.48  thf('26', plain, ((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['14', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i, X3 : $i]:
% 0.21/0.48         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.48  thf('28', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.48         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['20'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.21/0.48       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_D))),
% 0.21/0.48      inference('split', [status(esa)], ['20'])).
% 0.21/0.48  thf('31', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['22', '30'])).
% 0.21/0.48  thf('32', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['29', '31'])).
% 0.21/0.48  thf('33', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['28', '32'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
