%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MsIEW5hlR6

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:26 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  256 ( 322 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t2_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
           => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_tex_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_zfmisc_1 @ X28 )
      | ( X29 = X28 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ( X19 = X20 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
      | ~ ( v1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ X18 )
      | ( ( k4_xboole_0 @ X16 @ X18 )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( sk_A != sk_A )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MsIEW5hlR6
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:52:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.81/2.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.81/2.01  % Solved by: fo/fo7.sh
% 1.81/2.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.81/2.01  % done 3083 iterations in 1.562s
% 1.81/2.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.81/2.01  % SZS output start Refutation
% 1.81/2.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.81/2.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.81/2.01  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.81/2.01  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.81/2.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.81/2.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.81/2.01  thf(sk_B_type, type, sk_B: $i > $i).
% 1.81/2.01  thf(sk_A_type, type, sk_A: $i).
% 1.81/2.01  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.81/2.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.81/2.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.81/2.01  thf(t2_tex_2, conjecture,
% 1.81/2.01    (![A:$i]:
% 1.81/2.01     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.81/2.01       ( ![B:$i]:
% 1.81/2.01         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 1.81/2.01           ( r1_tarski @ A @ B ) ) ) ))).
% 1.81/2.01  thf(zf_stmt_0, negated_conjecture,
% 1.81/2.01    (~( ![A:$i]:
% 1.81/2.01        ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.81/2.01          ( ![B:$i]:
% 1.81/2.01            ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 1.81/2.01              ( r1_tarski @ A @ B ) ) ) ) )),
% 1.81/2.01    inference('cnf.neg', [status(esa)], [t2_tex_2])).
% 1.81/2.01  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 1.81/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.01  thf(t36_xboole_1, axiom,
% 1.81/2.01    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.81/2.01  thf('1', plain,
% 1.81/2.01      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.81/2.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.81/2.01  thf(t1_tex_2, axiom,
% 1.81/2.01    (![A:$i]:
% 1.81/2.01     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.81/2.01       ( ![B:$i]:
% 1.81/2.01         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.81/2.01           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 1.81/2.01  thf('2', plain,
% 1.81/2.01      (![X28 : $i, X29 : $i]:
% 1.81/2.01         ((v1_xboole_0 @ X28)
% 1.81/2.01          | ~ (v1_zfmisc_1 @ X28)
% 1.81/2.01          | ((X29) = (X28))
% 1.81/2.01          | ~ (r1_tarski @ X29 @ X28)
% 1.81/2.01          | (v1_xboole_0 @ X29))),
% 1.81/2.01      inference('cnf', [status(esa)], [t1_tex_2])).
% 1.81/2.01  thf('3', plain,
% 1.81/2.01      (![X0 : $i, X1 : $i]:
% 1.81/2.01         ((v1_xboole_0 @ (k4_xboole_0 @ X0 @ X1))
% 1.81/2.01          | ((k4_xboole_0 @ X0 @ X1) = (X0))
% 1.81/2.01          | ~ (v1_zfmisc_1 @ X0)
% 1.81/2.01          | (v1_xboole_0 @ X0))),
% 1.81/2.01      inference('sup-', [status(thm)], ['1', '2'])).
% 1.81/2.01  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.81/2.01  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.01      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.81/2.01  thf(t8_boole, axiom,
% 1.81/2.01    (![A:$i,B:$i]:
% 1.81/2.01     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.81/2.01  thf('5', plain,
% 1.81/2.01      (![X19 : $i, X20 : $i]:
% 1.81/2.01         (~ (v1_xboole_0 @ X19) | ~ (v1_xboole_0 @ X20) | ((X19) = (X20)))),
% 1.81/2.01      inference('cnf', [status(esa)], [t8_boole])).
% 1.81/2.01  thf('6', plain,
% 1.81/2.01      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.01      inference('sup-', [status(thm)], ['4', '5'])).
% 1.81/2.01  thf('7', plain,
% 1.81/2.01      (![X0 : $i, X1 : $i]:
% 1.81/2.01         ((v1_xboole_0 @ X1)
% 1.81/2.01          | ~ (v1_zfmisc_1 @ X1)
% 1.81/2.01          | ((k4_xboole_0 @ X1 @ X0) = (X1))
% 1.81/2.01          | ((k1_xboole_0) = (k4_xboole_0 @ X1 @ X0)))),
% 1.81/2.01      inference('sup-', [status(thm)], ['3', '6'])).
% 1.81/2.01  thf('8', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.81/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.01  thf('9', plain,
% 1.81/2.01      (![X0 : $i]:
% 1.81/2.01         (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ X0))
% 1.81/2.01          | ((k4_xboole_0 @ sk_A @ X0) = (sk_A))
% 1.81/2.01          | ~ (v1_zfmisc_1 @ sk_A))),
% 1.81/2.01      inference('sup-', [status(thm)], ['7', '8'])).
% 1.81/2.01  thf('10', plain, ((v1_zfmisc_1 @ sk_A)),
% 1.81/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.01  thf('11', plain,
% 1.81/2.01      (![X0 : $i]:
% 1.81/2.01         (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ X0))
% 1.81/2.01          | ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))),
% 1.81/2.01      inference('demod', [status(thm)], ['9', '10'])).
% 1.81/2.01  thf(t83_xboole_1, axiom,
% 1.81/2.01    (![A:$i,B:$i]:
% 1.81/2.01     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.81/2.01  thf('12', plain,
% 1.81/2.01      (![X16 : $i, X18 : $i]:
% 1.81/2.01         ((r1_xboole_0 @ X16 @ X18) | ((k4_xboole_0 @ X16 @ X18) != (X16)))),
% 1.81/2.01      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.81/2.01  thf('13', plain,
% 1.81/2.01      (![X0 : $i]:
% 1.81/2.01         (((sk_A) != (sk_A))
% 1.81/2.01          | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ X0))
% 1.81/2.01          | (r1_xboole_0 @ sk_A @ X0))),
% 1.81/2.01      inference('sup-', [status(thm)], ['11', '12'])).
% 1.81/2.01  thf('14', plain,
% 1.81/2.01      (![X0 : $i]:
% 1.81/2.01         ((r1_xboole_0 @ sk_A @ X0)
% 1.81/2.01          | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ X0)))),
% 1.81/2.01      inference('simplify', [status(thm)], ['13'])).
% 1.81/2.01  thf(d1_xboole_0, axiom,
% 1.81/2.01    (![A:$i]:
% 1.81/2.01     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.81/2.01  thf('15', plain,
% 1.81/2.01      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.81/2.01      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.81/2.01  thf(t4_xboole_0, axiom,
% 1.81/2.01    (![A:$i,B:$i]:
% 1.81/2.01     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.81/2.01            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.81/2.01       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.81/2.01            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.81/2.01  thf('16', plain,
% 1.81/2.01      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.81/2.01         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 1.81/2.01          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.81/2.01      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.81/2.01  thf('17', plain,
% 1.81/2.01      (![X0 : $i, X1 : $i]:
% 1.81/2.01         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.81/2.01      inference('sup-', [status(thm)], ['15', '16'])).
% 1.81/2.01  thf('18', plain,
% 1.81/2.01      (![X0 : $i]:
% 1.81/2.01         (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ X0))
% 1.81/2.01          | (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.81/2.01      inference('sup-', [status(thm)], ['14', '17'])).
% 1.81/2.01  thf('19', plain, (~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 1.81/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.01  thf('20', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.81/2.01      inference('sup-', [status(thm)], ['18', '19'])).
% 1.81/2.01  thf(l32_xboole_1, axiom,
% 1.81/2.01    (![A:$i,B:$i]:
% 1.81/2.01     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.81/2.01  thf('21', plain,
% 1.81/2.01      (![X11 : $i, X12 : $i]:
% 1.81/2.01         ((r1_tarski @ X11 @ X12)
% 1.81/2.01          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 1.81/2.01      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.81/2.01  thf('22', plain,
% 1.81/2.01      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B_1))),
% 1.81/2.01      inference('sup-', [status(thm)], ['20', '21'])).
% 1.81/2.01  thf('23', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.81/2.01      inference('simplify', [status(thm)], ['22'])).
% 1.81/2.01  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 1.81/2.01  
% 1.81/2.01  % SZS output end Refutation
% 1.81/2.01  
% 1.81/2.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
