%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8tGEGUeFUA

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:12 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 108 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  392 ( 782 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t74_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t74_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('35',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8tGEGUeFUA
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 19:27:32 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 365 iterations in 0.159s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.40/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(t74_xboole_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.40/0.62          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.62        ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.40/0.62             ( r1_xboole_0 @ A @ B ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t74_xboole_1])).
% 0.40/0.62  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_2))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t48_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.40/0.62           = (k3_xboole_0 @ X21 @ X22))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf('2', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(d3_tarski, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (![X1 : $i, X3 : $i]:
% 0.40/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf(t4_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.40/0.62          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.40/0.62          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.62  thf('6', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['2', '5'])).
% 0.40/0.62  thf(t38_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.40/0.62       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i]:
% 0.40/0.62         (((X14) = (k1_xboole_0))
% 0.40/0.62          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.40/0.62  thf('8', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.62  thf(t50_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.40/0.62       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.40/0.62         ((k3_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 0.40/0.62           = (k4_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 0.40/0.62              (k3_xboole_0 @ X24 @ X26)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.40/0.62           = (k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.40/0.62  thf(t4_boole, axiom,
% 0.40/0.62    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X23 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X23) = (k1_xboole_0))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_boole])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.40/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['1', '12'])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X6 : $i, X7 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X6 @ X7)
% 0.40/0.62          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.62  thf(t21_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X10 : $i, X11 : $i]:
% 0.40/0.62         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.40/0.62  thf(t47_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X19 : $i, X20 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.40/0.62           = (k4_xboole_0 @ X19 @ X20))),
% 0.40/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X0 @ X0)
% 0.40/0.62           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.40/0.62           = (k3_xboole_0 @ X21 @ X22))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.40/0.62           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['17', '18'])).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.40/0.62           = (k3_xboole_0 @ X21 @ X22))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf('21', plain,
% 0.40/0.62      (![X10 : $i, X11 : $i]:
% 0.40/0.62         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.40/0.62  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.40/0.62          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X1 @ X0)
% 0.40/0.62          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['14', '24'])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 0.40/0.62             k1_xboole_0)
% 0.40/0.62          | (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['13', '25'])).
% 0.40/0.62  thf('27', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['1', '12'])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.40/0.62          | (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.40/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X21 : $i, X22 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.40/0.62           = (k3_xboole_0 @ X21 @ X22))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      (![X23 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X23) = (k1_xboole_0))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_boole])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('32', plain,
% 0.40/0.62      (![X6 : $i, X7 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X6 @ X7)
% 0.40/0.62          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.62  thf('33', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.40/0.62          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.40/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.40/0.62  thf('34', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.40/0.62          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.62  thf('36', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.62  thf('37', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.40/0.62  thf('39', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.40/0.62      inference('clc', [status(thm)], ['33', '38'])).
% 0.40/0.62  thf('40', plain,
% 0.40/0.62      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))),
% 0.40/0.62      inference('demod', [status(thm)], ['28', '39'])).
% 0.40/0.62  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
