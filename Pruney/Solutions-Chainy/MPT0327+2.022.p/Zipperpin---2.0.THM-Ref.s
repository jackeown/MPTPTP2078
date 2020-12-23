%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ve89vDPv0d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:52 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   41 (  71 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  427 ( 886 expanded)
%              Number of equality atoms :   45 (  90 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ X1 ) @ X1 )
      | ( X2
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ X2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
      | ( ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 )
        = X1 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 )
        = X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_D @ X0 @ ( k1_tarski @ X1 ) @ X0 )
        = X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('12',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15 != X14 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_tarski @ X14 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( X1
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ve89vDPv0d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:44:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.47/1.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.47/1.66  % Solved by: fo/fo7.sh
% 1.47/1.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.47/1.66  % done 1738 iterations in 1.207s
% 1.47/1.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.47/1.66  % SZS output start Refutation
% 1.47/1.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.47/1.66  thf(sk_A_type, type, sk_A: $i).
% 1.47/1.66  thf(sk_B_type, type, sk_B: $i).
% 1.47/1.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.47/1.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.47/1.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.47/1.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.47/1.66  thf(t140_zfmisc_1, conjecture,
% 1.47/1.66    (![A:$i,B:$i]:
% 1.47/1.66     ( ( r2_hidden @ A @ B ) =>
% 1.47/1.66       ( ( k2_xboole_0 @
% 1.47/1.66           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.47/1.66         ( B ) ) ))).
% 1.47/1.66  thf(zf_stmt_0, negated_conjecture,
% 1.47/1.66    (~( ![A:$i,B:$i]:
% 1.47/1.66        ( ( r2_hidden @ A @ B ) =>
% 1.47/1.66          ( ( k2_xboole_0 @
% 1.47/1.66              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 1.47/1.66            ( B ) ) ) )),
% 1.47/1.66    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 1.47/1.66  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.47/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.66  thf(d3_xboole_0, axiom,
% 1.47/1.66    (![A:$i,B:$i,C:$i]:
% 1.47/1.66     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.47/1.66       ( ![D:$i]:
% 1.47/1.66         ( ( r2_hidden @ D @ C ) <=>
% 1.47/1.66           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.47/1.66  thf('1', plain,
% 1.47/1.66      (![X3 : $i, X5 : $i, X7 : $i]:
% 1.47/1.66         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 1.47/1.66          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 1.47/1.66          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 1.47/1.66          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 1.47/1.66      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.47/1.66  thf(d1_tarski, axiom,
% 1.47/1.66    (![A:$i,B:$i]:
% 1.47/1.66     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.47/1.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.47/1.66  thf('2', plain,
% 1.47/1.66      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.47/1.66         (~ (r2_hidden @ X17 @ X16)
% 1.47/1.66          | ((X17) = (X14))
% 1.47/1.66          | ((X16) != (k1_tarski @ X14)))),
% 1.47/1.66      inference('cnf', [status(esa)], [d1_tarski])).
% 1.47/1.66  thf('3', plain,
% 1.47/1.66      (![X14 : $i, X17 : $i]:
% 1.47/1.66         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 1.47/1.66      inference('simplify', [status(thm)], ['2'])).
% 1.47/1.66  thf('4', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.47/1.66         ((r2_hidden @ (sk_D @ X2 @ (k1_tarski @ X0) @ X1) @ X2)
% 1.47/1.66          | (r2_hidden @ (sk_D @ X2 @ (k1_tarski @ X0) @ X1) @ X1)
% 1.47/1.66          | ((X2) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.47/1.66          | ((sk_D @ X2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.47/1.66      inference('sup-', [status(thm)], ['1', '3'])).
% 1.47/1.66  thf('5', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (((sk_D @ X0 @ (k1_tarski @ X1) @ X0) = (X1))
% 1.47/1.66          | ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.47/1.66          | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ X1) @ X0) @ X0))),
% 1.47/1.66      inference('eq_fact', [status(thm)], ['4'])).
% 1.47/1.66  thf('6', plain,
% 1.47/1.66      (![X3 : $i, X5 : $i, X7 : $i]:
% 1.47/1.66         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 1.47/1.66          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 1.47/1.66          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 1.47/1.66      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.47/1.66  thf('7', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.47/1.66          | ((sk_D @ X0 @ (k1_tarski @ X1) @ X0) = (X1))
% 1.47/1.66          | ~ (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ X1) @ X0) @ X0)
% 1.47/1.66          | ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 1.47/1.66      inference('sup-', [status(thm)], ['5', '6'])).
% 1.47/1.66  thf('8', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (~ (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ X1) @ X0) @ X0)
% 1.47/1.66          | ((sk_D @ X0 @ (k1_tarski @ X1) @ X0) = (X1))
% 1.47/1.66          | ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 1.47/1.66      inference('simplify', [status(thm)], ['7'])).
% 1.47/1.66  thf('9', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (((sk_D @ X0 @ (k1_tarski @ X1) @ X0) = (X1))
% 1.47/1.66          | ((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.47/1.66          | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ X1) @ X0) @ X0))),
% 1.47/1.66      inference('eq_fact', [status(thm)], ['4'])).
% 1.47/1.66  thf('10', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.47/1.66          | ((sk_D @ X0 @ (k1_tarski @ X1) @ X0) = (X1)))),
% 1.47/1.66      inference('clc', [status(thm)], ['8', '9'])).
% 1.47/1.66  thf('11', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (((X0) = (k2_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.47/1.66          | ((sk_D @ X0 @ (k1_tarski @ X1) @ X0) = (X1)))),
% 1.47/1.66      inference('clc', [status(thm)], ['8', '9'])).
% 1.47/1.66  thf('12', plain,
% 1.47/1.66      (![X3 : $i, X5 : $i, X7 : $i]:
% 1.47/1.66         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 1.47/1.66          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 1.47/1.66          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 1.47/1.66      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.47/1.66  thf('13', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.47/1.66          | ((X1) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.47/1.66          | ~ (r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X1) @ X1)
% 1.47/1.66          | ((X1) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.47/1.66      inference('sup-', [status(thm)], ['11', '12'])).
% 1.47/1.66  thf('14', plain,
% 1.47/1.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.47/1.66         (((X15) != (X14))
% 1.47/1.66          | (r2_hidden @ X15 @ X16)
% 1.47/1.66          | ((X16) != (k1_tarski @ X14)))),
% 1.47/1.66      inference('cnf', [status(esa)], [d1_tarski])).
% 1.47/1.66  thf('15', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_tarski @ X14))),
% 1.47/1.66      inference('simplify', [status(thm)], ['14'])).
% 1.47/1.66  thf('16', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (((X1) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.47/1.66          | ~ (r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X1) @ X1)
% 1.47/1.66          | ((X1) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.47/1.66      inference('demod', [status(thm)], ['13', '15'])).
% 1.47/1.66  thf('17', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (~ (r2_hidden @ (sk_D @ X1 @ (k1_tarski @ X0) @ X1) @ X1)
% 1.47/1.66          | ((X1) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.47/1.66      inference('simplify', [status(thm)], ['16'])).
% 1.47/1.66  thf('18', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (~ (r2_hidden @ X0 @ X1)
% 1.47/1.66          | ((X1) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.47/1.66          | ((X1) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.47/1.66      inference('sup-', [status(thm)], ['10', '17'])).
% 1.47/1.66  thf('19', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]:
% 1.47/1.66         (((X1) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.47/1.66          | ~ (r2_hidden @ X0 @ X1))),
% 1.47/1.66      inference('simplify', [status(thm)], ['18'])).
% 1.47/1.66  thf('20', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.47/1.66      inference('sup-', [status(thm)], ['0', '19'])).
% 1.47/1.66  thf('21', plain,
% 1.47/1.66      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 1.47/1.66         (k1_tarski @ sk_A)) != (sk_B))),
% 1.47/1.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.47/1.66  thf(commutativity_k2_xboole_0, axiom,
% 1.47/1.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.47/1.66  thf('22', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.47/1.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.47/1.66  thf('23', plain,
% 1.47/1.66      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 1.47/1.66         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 1.47/1.66      inference('demod', [status(thm)], ['21', '22'])).
% 1.47/1.66  thf(t39_xboole_1, axiom,
% 1.47/1.66    (![A:$i,B:$i]:
% 1.47/1.66     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.47/1.66  thf('24', plain,
% 1.47/1.66      (![X10 : $i, X11 : $i]:
% 1.47/1.66         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.47/1.66           = (k2_xboole_0 @ X10 @ X11))),
% 1.47/1.66      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.47/1.66  thf('25', plain,
% 1.47/1.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.47/1.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.47/1.66  thf('26', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 1.47/1.66      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.47/1.66  thf('27', plain, ($false),
% 1.47/1.66      inference('simplify_reflect-', [status(thm)], ['20', '26'])).
% 1.47/1.66  
% 1.47/1.66  % SZS output end Refutation
% 1.47/1.66  
% 1.47/1.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
