%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qEqvGn9keT

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  273 ( 431 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('3',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X11: $i] :
      ( ( r1_xboole_0 @ X11 @ sk_B )
      | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('16',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) )
      | ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) )
      | ( r1_xboole_0 @ ( k3_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ sk_B )
    | ( r1_xboole_0 @ ( k3_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    r1_xboole_0 @ ( k3_tarski @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qEqvGn9keT
% 0.14/0.36  % Computer   : n009.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:23:56 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 95 iterations in 0.067s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.22/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.54  thf(t98_zfmisc_1, conjecture,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 0.22/0.54       ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i]:
% 0.22/0.54        ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_xboole_0 @ C @ B ) ) ) =>
% 0.22/0.54          ( r1_xboole_0 @ ( k3_tarski @ A ) @ B ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t98_zfmisc_1])).
% 0.22/0.54  thf('0', plain, (~ (r1_xboole_0 @ (k3_tarski @ sk_A) @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t3_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.54  thf(d4_tarski, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.22/0.54       ( ![C:$i]:
% 0.22/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.54           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X8 @ X7)
% 0.22/0.54          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 0.22/0.54          | ((X7) != (k3_tarski @ X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_tarski])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X5 : $i, X8 : $i]:
% 0.22/0.54         ((r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 0.22/0.54          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ (k3_tarski @ X0) @ X1)
% 0.22/0.54          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '3'])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X11 : $i]: ((r1_xboole_0 @ X11 @ sk_B) | ~ (r2_hidden @ X11 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ (k3_tarski @ sk_A) @ X0)
% 0.22/0.54          | (r1_xboole_0 @ 
% 0.22/0.54             (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.54          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.54          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.54          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.54          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.54          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.22/0.54          | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ (k3_tarski @ sk_A) @ X0)
% 0.22/0.54          | (r1_xboole_0 @ sk_B @ 
% 0.22/0.54             (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '12'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X8 @ X7)
% 0.22/0.54          | (r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 0.22/0.54          | ((X7) != (k3_tarski @ X5)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_tarski])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X5 : $i, X8 : $i]:
% 0.22/0.54         ((r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 0.22/0.54          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ (k3_tarski @ X0) @ X1)
% 0.22/0.54          | (r2_hidden @ (sk_C @ X1 @ (k3_tarski @ X0)) @ 
% 0.22/0.54             (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['14', '16'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.54          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.54          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((r1_xboole_0 @ (k3_tarski @ X0) @ X1)
% 0.22/0.54          | ~ (r1_xboole_0 @ X1 @ 
% 0.22/0.54               (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0))
% 0.22/0.54          | (r1_xboole_0 @ (k3_tarski @ X0) @ X1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r1_xboole_0 @ X1 @ (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0))
% 0.22/0.54          | (r1_xboole_0 @ (k3_tarski @ X0) @ X1))),
% 0.22/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (((r1_xboole_0 @ (k3_tarski @ sk_A) @ sk_B)
% 0.22/0.54        | (r1_xboole_0 @ (k3_tarski @ sk_A) @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['13', '20'])).
% 0.22/0.54  thf('22', plain, ((r1_xboole_0 @ (k3_tarski @ sk_A) @ sk_B)),
% 0.22/0.54      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.54  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
