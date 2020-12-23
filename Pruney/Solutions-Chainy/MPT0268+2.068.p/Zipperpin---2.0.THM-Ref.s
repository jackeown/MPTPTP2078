%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SgkDafLhrz

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:01 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   45 (  82 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  384 ( 753 expanded)
%              Number of equality atoms :   35 (  71 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X11 )
      | ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X6 ) @ X8 )
        = ( k1_tarski @ X6 ) )
      | ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','25'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','9','28'])).

thf('30',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('31',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['11','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SgkDafLhrz
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:42:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.03/1.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.03/1.23  % Solved by: fo/fo7.sh
% 1.03/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.23  % done 1247 iterations in 0.769s
% 1.03/1.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.03/1.23  % SZS output start Refutation
% 1.03/1.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.03/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.03/1.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.03/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.23  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.03/1.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.03/1.23  thf(t65_zfmisc_1, conjecture,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.03/1.23       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.03/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.23    (~( ![A:$i,B:$i]:
% 1.03/1.23        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.03/1.23          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.03/1.23    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.03/1.23  thf('0', plain,
% 1.03/1.23      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.03/1.23        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('1', plain,
% 1.03/1.23      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.03/1.23      inference('split', [status(esa)], ['0'])).
% 1.03/1.23  thf('2', plain,
% 1.03/1.23      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.03/1.23       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.03/1.23      inference('split', [status(esa)], ['0'])).
% 1.03/1.23  thf('3', plain,
% 1.03/1.23      (((r2_hidden @ sk_B @ sk_A)
% 1.03/1.23        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('4', plain,
% 1.03/1.23      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.03/1.23      inference('split', [status(esa)], ['3'])).
% 1.03/1.23  thf('5', plain,
% 1.03/1.23      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.03/1.23         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.03/1.23      inference('split', [status(esa)], ['0'])).
% 1.03/1.23  thf(t64_zfmisc_1, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 1.03/1.23       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 1.03/1.23  thf('6', plain,
% 1.03/1.23      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.03/1.23         (((X9) != (X11))
% 1.03/1.23          | ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X10 @ (k1_tarski @ X11))))),
% 1.03/1.23      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 1.03/1.23  thf('7', plain,
% 1.03/1.23      (![X10 : $i, X11 : $i]:
% 1.03/1.23         ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X10 @ (k1_tarski @ X11)))),
% 1.03/1.23      inference('simplify', [status(thm)], ['6'])).
% 1.03/1.23  thf('8', plain,
% 1.03/1.23      ((~ (r2_hidden @ sk_B @ sk_A))
% 1.03/1.23         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['5', '7'])).
% 1.03/1.23  thf('9', plain,
% 1.03/1.23      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.03/1.23       ~ ((r2_hidden @ sk_B @ sk_A))),
% 1.03/1.23      inference('sup-', [status(thm)], ['4', '8'])).
% 1.03/1.23  thf('10', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 1.03/1.23      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 1.03/1.23  thf('11', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.03/1.23      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 1.03/1.23  thf(l33_zfmisc_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.03/1.23       ( ~( r2_hidden @ A @ B ) ) ))).
% 1.03/1.23  thf('12', plain,
% 1.03/1.23      (![X6 : $i, X8 : $i]:
% 1.03/1.23         (((k4_xboole_0 @ (k1_tarski @ X6) @ X8) = (k1_tarski @ X6))
% 1.03/1.23          | (r2_hidden @ X6 @ X8))),
% 1.03/1.23      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 1.03/1.23  thf(d5_xboole_0, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.03/1.23       ( ![D:$i]:
% 1.03/1.23         ( ( r2_hidden @ D @ C ) <=>
% 1.03/1.23           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.03/1.23  thf('13', plain,
% 1.03/1.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.23         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.03/1.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.23  thf('14', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.23      inference('eq_fact', [status(thm)], ['13'])).
% 1.03/1.23  thf('15', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.23      inference('eq_fact', [status(thm)], ['13'])).
% 1.03/1.23  thf('16', plain,
% 1.03/1.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.03/1.23         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.03/1.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.03/1.23          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.03/1.23          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.03/1.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.03/1.23  thf('17', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.03/1.23          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.23          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.03/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['15', '16'])).
% 1.03/1.23  thf('18', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.03/1.23          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.03/1.23      inference('simplify', [status(thm)], ['17'])).
% 1.03/1.23  thf('19', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.03/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.06/1.23      inference('eq_fact', [status(thm)], ['13'])).
% 1.06/1.23  thf('20', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.06/1.23          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.06/1.23      inference('clc', [status(thm)], ['18', '19'])).
% 1.06/1.23  thf('21', plain,
% 1.06/1.23      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.23         (~ (r2_hidden @ X4 @ X3)
% 1.06/1.23          | ~ (r2_hidden @ X4 @ X2)
% 1.06/1.23          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.06/1.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.06/1.23  thf('22', plain,
% 1.06/1.23      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.06/1.23         (~ (r2_hidden @ X4 @ X2)
% 1.06/1.23          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.06/1.23      inference('simplify', [status(thm)], ['21'])).
% 1.06/1.23  thf('23', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.23         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.06/1.23          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 1.06/1.23      inference('sup-', [status(thm)], ['20', '22'])).
% 1.06/1.23  thf('24', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.06/1.23          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.06/1.23      inference('sup-', [status(thm)], ['14', '23'])).
% 1.06/1.23  thf('25', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.06/1.23      inference('simplify', [status(thm)], ['24'])).
% 1.06/1.23  thf('26', plain,
% 1.06/1.23      (![X0 : $i, X1 : $i]:
% 1.06/1.23         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.06/1.23          | (r2_hidden @ X0 @ X1))),
% 1.06/1.23      inference('sup+', [status(thm)], ['12', '25'])).
% 1.06/1.23  thf('27', plain,
% 1.06/1.23      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.06/1.23         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.06/1.23      inference('split', [status(esa)], ['3'])).
% 1.06/1.23  thf('28', plain,
% 1.06/1.23      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.06/1.23       ((r2_hidden @ sk_B @ sk_A))),
% 1.06/1.23      inference('split', [status(esa)], ['3'])).
% 1.06/1.23  thf('29', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.06/1.23      inference('sat_resolution*', [status(thm)], ['2', '9', '28'])).
% 1.06/1.23  thf('30', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 1.06/1.23      inference('simpl_trail', [status(thm)], ['27', '29'])).
% 1.06/1.23  thf('31', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 1.06/1.23      inference('sup-', [status(thm)], ['26', '30'])).
% 1.06/1.23  thf('32', plain, ((r2_hidden @ sk_B @ sk_A)),
% 1.06/1.23      inference('simplify', [status(thm)], ['31'])).
% 1.06/1.23  thf('33', plain, ($false), inference('demod', [status(thm)], ['11', '32'])).
% 1.06/1.23  
% 1.06/1.23  % SZS output end Refutation
% 1.06/1.23  
% 1.06/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
