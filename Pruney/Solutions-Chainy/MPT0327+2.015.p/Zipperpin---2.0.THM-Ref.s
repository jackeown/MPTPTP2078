%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WMkw6sRQXk

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:51 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   55 (  86 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  473 ( 904 expanded)
%              Number of equality atoms :   48 (  80 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( X22 = X19 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22 = X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k4_xboole_0 @ X2 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['25','29'])).

thf('31',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','30'])).

thf('32',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WMkw6sRQXk
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:39:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.83  % Solved by: fo/fo7.sh
% 0.59/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.83  % done 399 iterations in 0.379s
% 0.59/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.83  % SZS output start Refutation
% 0.59/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.83  thf(t140_zfmisc_1, conjecture,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( r2_hidden @ A @ B ) =>
% 0.59/0.83       ( ( k2_xboole_0 @
% 0.59/0.83           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.59/0.83         ( B ) ) ))).
% 0.59/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.83    (~( ![A:$i,B:$i]:
% 0.59/0.83        ( ( r2_hidden @ A @ B ) =>
% 0.59/0.83          ( ( k2_xboole_0 @
% 0.59/0.83              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.59/0.83            ( B ) ) ) )),
% 0.59/0.83    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.59/0.83  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(d5_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.59/0.83       ( ![D:$i]:
% 0.59/0.83         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.83           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.59/0.83  thf('1', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.59/0.83         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.59/0.83          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.59/0.83          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.59/0.83      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.83  thf('2', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.59/0.83         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.59/0.83          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.59/0.83          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.59/0.83      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.83  thf('3', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.59/0.83          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.59/0.83          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.59/0.83          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.83  thf('4', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.59/0.83          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.59/0.83      inference('simplify', [status(thm)], ['3'])).
% 0.59/0.83  thf('5', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X6 @ X5)
% 0.59/0.83          | (r2_hidden @ X6 @ X3)
% 0.59/0.83          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.59/0.83      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.83  thf('6', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.59/0.83         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['5'])).
% 0.59/0.83  thf('7', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.59/0.83          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['4', '6'])).
% 0.59/0.83  thf(d1_tarski, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.59/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.59/0.83  thf('8', plain,
% 0.59/0.83      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X22 @ X21)
% 0.59/0.83          | ((X22) = (X19))
% 0.59/0.83          | ((X21) != (k1_tarski @ X19)))),
% 0.59/0.83      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.83  thf('9', plain,
% 0.59/0.83      (![X19 : $i, X22 : $i]:
% 0.59/0.83         (((X22) = (X19)) | ~ (r2_hidden @ X22 @ (k1_tarski @ X19)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['8'])).
% 0.59/0.83  thf('10', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k4_xboole_0 @ X1 @ X1))
% 0.59/0.83          | ((sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ X1) = (X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['7', '9'])).
% 0.59/0.83  thf('11', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.59/0.83          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.59/0.83      inference('simplify', [status(thm)], ['3'])).
% 0.59/0.83  thf('12', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X6 @ X5)
% 0.59/0.83          | ~ (r2_hidden @ X6 @ X4)
% 0.59/0.83          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.59/0.83      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.83  thf('13', plain,
% 0.59/0.83      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X6 @ X4)
% 0.59/0.83          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.59/0.83      inference('simplify', [status(thm)], ['12'])).
% 0.59/0.83  thf('14', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.59/0.83          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['11', '13'])).
% 0.59/0.83  thf('15', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.83          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k4_xboole_0 @ X2 @ X2))
% 0.59/0.83          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k4_xboole_0 @ X2 @ X2)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['10', '14'])).
% 0.59/0.83  thf('16', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k4_xboole_0 @ X2 @ X2))
% 0.59/0.83          | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.83      inference('simplify', [status(thm)], ['15'])).
% 0.59/0.83  thf('17', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['0', '16'])).
% 0.59/0.83  thf(t39_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.83  thf('18', plain,
% 0.59/0.83      (![X15 : $i, X16 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.59/0.83           = (k2_xboole_0 @ X15 @ X16))),
% 0.59/0.83      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.83  thf('19', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ X0))
% 0.59/0.83           = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.83  thf('20', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.59/0.83          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['4', '6'])).
% 0.59/0.83  thf('21', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X2))
% 0.59/0.83          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['11', '13'])).
% 0.59/0.83  thf('22', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.59/0.83          | ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.83  thf('23', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 0.59/0.83      inference('simplify', [status(thm)], ['22'])).
% 0.59/0.83  thf('24', plain,
% 0.59/0.83      (![X15 : $i, X16 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.59/0.83           = (k2_xboole_0 @ X15 @ X16))),
% 0.59/0.83      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.83  thf('25', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.59/0.83           = (k2_xboole_0 @ X1 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.83  thf(d10_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.83  thf('26', plain,
% 0.59/0.83      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.59/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.83  thf('27', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.59/0.83      inference('simplify', [status(thm)], ['26'])).
% 0.59/0.83  thf(t12_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.59/0.83  thf('28', plain,
% 0.59/0.83      (![X13 : $i, X14 : $i]:
% 0.59/0.83         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.59/0.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.83  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['27', '28'])).
% 0.59/0.83  thf('30', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['25', '29'])).
% 0.59/0.83  thf('31', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.59/0.83      inference('demod', [status(thm)], ['19', '30'])).
% 0.59/0.83  thf('32', plain,
% 0.59/0.83      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.59/0.83         (k1_tarski @ sk_A)) != (sk_B))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(commutativity_k2_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.59/0.83  thf('33', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.83  thf('34', plain,
% 0.59/0.83      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.59/0.83         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.83  thf('35', plain,
% 0.59/0.83      (![X15 : $i, X16 : $i]:
% 0.59/0.83         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.59/0.83           = (k2_xboole_0 @ X15 @ X16))),
% 0.59/0.83      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.83  thf('36', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.83  thf('37', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.59/0.83  thf('38', plain, ($false),
% 0.59/0.83      inference('simplify_reflect-', [status(thm)], ['31', '37'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.59/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
