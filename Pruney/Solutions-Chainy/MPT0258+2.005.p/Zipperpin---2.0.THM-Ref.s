%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.89rbtNDpTU

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:24 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   35 (  56 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 520 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t53_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k2_tarski @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_zfmisc_1])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X13 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ ( sk_D @ X7 @ X6 @ X5 ) @ X7 )
      | ( X5
        = ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_C )
        = ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( sk_D @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) @ ( k2_tarski @ sk_A @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( sk_D @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) @ ( k2_tarski @ sk_A @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ~ ( r1_tarski @ ( sk_D @ X7 @ X6 @ X5 ) @ X5 )
      | ( X5
        = ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('15',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ ( k2_tarski @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('17',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf('18',plain,
    ( ( k2_tarski @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.89rbtNDpTU
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:32:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 286 iterations in 0.173s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(d10_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.63  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.45/0.63      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.64  thf(t53_zfmisc_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.45/0.64       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.64        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.45/0.64          ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t53_zfmisc_1])).
% 0.45/0.64  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('3', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t38_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.45/0.64       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.45/0.64         ((r1_tarski @ (k2_tarski @ X13 @ X15) @ X16)
% 0.45/0.64          | ~ (r2_hidden @ X15 @ X16)
% 0.45/0.64          | ~ (r2_hidden @ X13 @ X16))),
% 0.45/0.64      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X0 @ sk_B)
% 0.45/0.64          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf('6', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '5'])).
% 0.45/0.64  thf(t20_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.45/0.64         ( ![D:$i]:
% 0.45/0.64           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.45/0.64             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.45/0.64       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X5 @ X6)
% 0.45/0.64          | ~ (r1_tarski @ X5 @ X7)
% 0.45/0.64          | (r1_tarski @ (sk_D @ X7 @ X6 @ X5) @ X7)
% 0.45/0.64          | ((X5) = (k3_xboole_0 @ X6 @ X7)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k2_tarski @ sk_A @ sk_C) = (k3_xboole_0 @ sk_B @ X0))
% 0.45/0.64          | (r1_tarski @ (sk_D @ X0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) @ X0)
% 0.45/0.64          | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (((r1_tarski @ 
% 0.45/0.64         (sk_D @ (k2_tarski @ sk_A @ sk_C) @ sk_B @ (k2_tarski @ sk_A @ sk_C)) @ 
% 0.45/0.64         (k2_tarski @ sk_A @ sk_C))
% 0.45/0.64        | ((k2_tarski @ sk_A @ sk_C)
% 0.45/0.64            = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '8'])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.45/0.64         != (k2_tarski @ sk_A @ sk_C))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.45/0.64         != (k2_tarski @ sk_A @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      ((r1_tarski @ 
% 0.45/0.64        (sk_D @ (k2_tarski @ sk_A @ sk_C) @ sk_B @ (k2_tarski @ sk_A @ sk_C)) @ 
% 0.45/0.64        (k2_tarski @ sk_A @ sk_C))),
% 0.45/0.64      inference('simplify_reflect-', [status(thm)], ['9', '12'])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X5 @ X6)
% 0.45/0.64          | ~ (r1_tarski @ X5 @ X7)
% 0.45/0.64          | ~ (r1_tarski @ (sk_D @ X7 @ X6 @ X5) @ X5)
% 0.45/0.64          | ((X5) = (k3_xboole_0 @ X6 @ X7)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      ((((k2_tarski @ sk_A @ sk_C)
% 0.45/0.64          = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 0.45/0.64        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ (k2_tarski @ sk_A @ sk_C))
% 0.45/0.64        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.64  thf('16', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.45/0.64      inference('simplify', [status(thm)], ['0'])).
% 0.45/0.64  thf('17', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '5'])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (((k2_tarski @ sk_A @ sk_C)
% 0.45/0.64         = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 0.45/0.64      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.45/0.64         != (k2_tarski @ sk_A @ sk_C))),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf('20', plain, ($false),
% 0.45/0.64      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
