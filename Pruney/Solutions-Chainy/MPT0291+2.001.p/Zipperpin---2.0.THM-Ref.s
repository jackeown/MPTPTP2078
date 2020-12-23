%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Urltjn97DS

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:54 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   41 (  53 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  347 ( 499 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t98_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ! [C: $i] :
            ( ( r2_hidden @ C @ A )
           => ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t98_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( sk_D_2 @ X14 @ X11 ) @ X11 )
      | ( X13
       != ( k3_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('6',plain,(
    ! [X11: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X14 @ X11 ) @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k3_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X17: $i] :
      ( ( r1_xboole_0 @ X17 @ sk_B )
      | ~ ( r2_hidden @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ ( sk_D_2 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('11',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ X14 @ ( sk_D_2 @ X14 @ X11 ) )
      | ( X13
       != ( k3_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('12',plain,(
    ! [X11: $i,X14: $i] :
      ( ( r2_hidden @ X14 @ ( sk_D_2 @ X14 @ X11 ) )
      | ~ ( r2_hidden @ X14 @ ( k3_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ ( sk_D_2 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ ( k3_xboole_0 @ ( sk_D_2 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X1 ) )
      | ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ ( k3_xboole_0 @ ( sk_D_2 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X1 ) )
      | ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X1 ) @ X0 )
      | ~ ( r1_xboole_0 @ ( sk_D_2 @ ( sk_C @ X0 @ ( k3_tarski @ X1 ) ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ sk_B )
    | ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Urltjn97DS
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:46:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 2.03/2.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.03/2.25  % Solved by: fo/fo7.sh
% 2.03/2.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.03/2.25  % done 2071 iterations in 1.800s
% 2.03/2.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.03/2.25  % SZS output start Refutation
% 2.03/2.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.03/2.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.03/2.25  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.03/2.25  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.03/2.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.03/2.25  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 2.03/2.25  thf(sk_B_type, type, sk_B: $i).
% 2.03/2.25  thf(sk_A_type, type, sk_A: $i).
% 2.03/2.25  thf(t98_zfmisc_1, conjecture,
% 2.03/2.25    (![A:$i,B:$i]:
% 2.03/2.25     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 2.03/2.25       ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ))).
% 2.03/2.25  thf(zf_stmt_0, negated_conjecture,
% 2.03/2.25    (~( ![A:$i,B:$i]:
% 2.03/2.25        ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 2.03/2.25          ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )),
% 2.03/2.25    inference('cnf.neg', [status(esa)], [t98_zfmisc_1])).
% 2.03/2.25  thf('0', plain, (~ (r1_xboole_0 @ (k3_tarski @ sk_A) @ sk_B)),
% 2.03/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.25  thf(t4_xboole_0, axiom,
% 2.03/2.25    (![A:$i,B:$i]:
% 2.03/2.25     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.03/2.25            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.03/2.25       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.03/2.25            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.03/2.25  thf('1', plain,
% 2.03/2.25      (![X6 : $i, X7 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ X6 @ X7)
% 2.03/2.25          | (r2_hidden @ (sk_C @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 2.03/2.25      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.03/2.25  thf(d4_xboole_0, axiom,
% 2.03/2.25    (![A:$i,B:$i,C:$i]:
% 2.03/2.25     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.03/2.25       ( ![D:$i]:
% 2.03/2.25         ( ( r2_hidden @ D @ C ) <=>
% 2.03/2.25           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.03/2.25  thf('2', plain,
% 2.03/2.25      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.03/2.25         (~ (r2_hidden @ X4 @ X3)
% 2.03/2.25          | (r2_hidden @ X4 @ X1)
% 2.03/2.25          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 2.03/2.25      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.03/2.25  thf('3', plain,
% 2.03/2.25      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.03/2.25         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.03/2.25      inference('simplify', [status(thm)], ['2'])).
% 2.03/2.25  thf('4', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 2.03/2.25      inference('sup-', [status(thm)], ['1', '3'])).
% 2.03/2.25  thf(d4_tarski, axiom,
% 2.03/2.25    (![A:$i,B:$i]:
% 2.03/2.25     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 2.03/2.25       ( ![C:$i]:
% 2.03/2.25         ( ( r2_hidden @ C @ B ) <=>
% 2.03/2.25           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 2.03/2.25  thf('5', plain,
% 2.03/2.25      (![X11 : $i, X13 : $i, X14 : $i]:
% 2.03/2.25         (~ (r2_hidden @ X14 @ X13)
% 2.03/2.25          | (r2_hidden @ (sk_D_2 @ X14 @ X11) @ X11)
% 2.03/2.25          | ((X13) != (k3_tarski @ X11)))),
% 2.03/2.25      inference('cnf', [status(esa)], [d4_tarski])).
% 2.03/2.25  thf('6', plain,
% 2.03/2.25      (![X11 : $i, X14 : $i]:
% 2.03/2.25         ((r2_hidden @ (sk_D_2 @ X14 @ X11) @ X11)
% 2.03/2.25          | ~ (r2_hidden @ X14 @ (k3_tarski @ X11)))),
% 2.03/2.25      inference('simplify', [status(thm)], ['5'])).
% 2.03/2.25  thf('7', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ (k3_tarski @ X0) @ X1)
% 2.03/2.25          | (r2_hidden @ (sk_D_2 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X0))),
% 2.03/2.25      inference('sup-', [status(thm)], ['4', '6'])).
% 2.03/2.25  thf('8', plain,
% 2.03/2.25      (![X17 : $i]: ((r1_xboole_0 @ X17 @ sk_B) | ~ (r2_hidden @ X17 @ sk_A))),
% 2.03/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.25  thf('9', plain,
% 2.03/2.25      (![X0 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ (k3_tarski @ sk_A) @ X0)
% 2.03/2.25          | (r1_xboole_0 @ 
% 2.03/2.25             (sk_D_2 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ sk_B))),
% 2.03/2.25      inference('sup-', [status(thm)], ['7', '8'])).
% 2.03/2.25  thf('10', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 2.03/2.25      inference('sup-', [status(thm)], ['1', '3'])).
% 2.03/2.25  thf('11', plain,
% 2.03/2.25      (![X11 : $i, X13 : $i, X14 : $i]:
% 2.03/2.25         (~ (r2_hidden @ X14 @ X13)
% 2.03/2.25          | (r2_hidden @ X14 @ (sk_D_2 @ X14 @ X11))
% 2.03/2.25          | ((X13) != (k3_tarski @ X11)))),
% 2.03/2.25      inference('cnf', [status(esa)], [d4_tarski])).
% 2.03/2.25  thf('12', plain,
% 2.03/2.25      (![X11 : $i, X14 : $i]:
% 2.03/2.25         ((r2_hidden @ X14 @ (sk_D_2 @ X14 @ X11))
% 2.03/2.25          | ~ (r2_hidden @ X14 @ (k3_tarski @ X11)))),
% 2.03/2.25      inference('simplify', [status(thm)], ['11'])).
% 2.03/2.25  thf('13', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ (k3_tarski @ X0) @ X1)
% 2.03/2.25          | (r2_hidden @ (sk_C @ X1 @ (k3_tarski @ X0)) @ 
% 2.03/2.25             (sk_D_2 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0)))),
% 2.03/2.25      inference('sup-', [status(thm)], ['10', '12'])).
% 2.03/2.25  thf('14', plain,
% 2.03/2.25      (![X6 : $i, X7 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ X6 @ X7)
% 2.03/2.25          | (r2_hidden @ (sk_C @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 2.03/2.25      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.03/2.25  thf('15', plain,
% 2.03/2.25      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.03/2.25         (~ (r2_hidden @ X4 @ X3)
% 2.03/2.25          | (r2_hidden @ X4 @ X2)
% 2.03/2.25          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 2.03/2.25      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.03/2.25  thf('16', plain,
% 2.03/2.25      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.03/2.25         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 2.03/2.25      inference('simplify', [status(thm)], ['15'])).
% 2.03/2.25  thf('17', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 2.03/2.25      inference('sup-', [status(thm)], ['14', '16'])).
% 2.03/2.25  thf('18', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.03/2.25         (~ (r2_hidden @ X0 @ X1)
% 2.03/2.25          | ~ (r2_hidden @ X0 @ X2)
% 2.03/2.25          | (r2_hidden @ X0 @ X3)
% 2.03/2.25          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 2.03/2.25      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.03/2.25  thf('19', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.25         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 2.03/2.25          | ~ (r2_hidden @ X0 @ X2)
% 2.03/2.25          | ~ (r2_hidden @ X0 @ X1))),
% 2.03/2.25      inference('simplify', [status(thm)], ['18'])).
% 2.03/2.25  thf('20', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ X1 @ X0)
% 2.03/2.25          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2)
% 2.03/2.25          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 2.03/2.25      inference('sup-', [status(thm)], ['17', '19'])).
% 2.03/2.25  thf('21', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ (k3_tarski @ X0) @ X1)
% 2.03/2.25          | (r2_hidden @ (sk_C @ X1 @ (k3_tarski @ X0)) @ 
% 2.03/2.25             (k3_xboole_0 @ (sk_D_2 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X1))
% 2.03/2.25          | (r1_xboole_0 @ (k3_tarski @ X0) @ X1))),
% 2.03/2.25      inference('sup-', [status(thm)], ['13', '20'])).
% 2.03/2.25  thf('22', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i]:
% 2.03/2.25         ((r2_hidden @ (sk_C @ X1 @ (k3_tarski @ X0)) @ 
% 2.03/2.25           (k3_xboole_0 @ (sk_D_2 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X1))
% 2.03/2.25          | (r1_xboole_0 @ (k3_tarski @ X0) @ X1))),
% 2.03/2.25      inference('simplify', [status(thm)], ['21'])).
% 2.03/2.25  thf('23', plain,
% 2.03/2.25      (![X6 : $i, X8 : $i, X9 : $i]:
% 2.03/2.25         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 2.03/2.25          | ~ (r1_xboole_0 @ X6 @ X9))),
% 2.03/2.25      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.03/2.25  thf('24', plain,
% 2.03/2.25      (![X0 : $i, X1 : $i]:
% 2.03/2.25         ((r1_xboole_0 @ (k3_tarski @ X1) @ X0)
% 2.03/2.25          | ~ (r1_xboole_0 @ (sk_D_2 @ (sk_C @ X0 @ (k3_tarski @ X1)) @ X1) @ 
% 2.03/2.25               X0))),
% 2.03/2.25      inference('sup-', [status(thm)], ['22', '23'])).
% 2.03/2.25  thf('25', plain,
% 2.03/2.25      (((r1_xboole_0 @ (k3_tarski @ sk_A) @ sk_B)
% 2.03/2.25        | (r1_xboole_0 @ (k3_tarski @ sk_A) @ sk_B))),
% 2.03/2.25      inference('sup-', [status(thm)], ['9', '24'])).
% 2.03/2.25  thf('26', plain, ((r1_xboole_0 @ (k3_tarski @ sk_A) @ sk_B)),
% 2.03/2.25      inference('simplify', [status(thm)], ['25'])).
% 2.03/2.25  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 2.03/2.25  
% 2.03/2.25  % SZS output end Refutation
% 2.03/2.25  
% 2.03/2.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
