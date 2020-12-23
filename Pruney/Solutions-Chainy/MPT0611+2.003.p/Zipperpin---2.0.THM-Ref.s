%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rRkgXAW53Z

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  273 ( 377 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t215_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t215_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t27_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X38 @ X37 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X38 ) @ ( k2_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t27_relat_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 ) ),
    inference(demod,[status(thm)],['8','11','12','13'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X13 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('16',plain,
    ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X39: $i] :
      ( ( ( k2_relat_1 @ X39 )
       != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rRkgXAW53Z
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 195 iterations in 0.063s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(t215_relat_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v1_relat_1 @ B ) =>
% 0.20/0.51           ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.51             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( v1_relat_1 @ A ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( v1_relat_1 @ B ) =>
% 0.20/0.51              ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.51                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t215_relat_1])).
% 0.20/0.51  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(fc1_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X28) | (v1_relat_1 @ (k3_xboole_0 @ X28 @ X29)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.20/0.51  thf('2', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d7_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.20/0.51         = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t27_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v1_relat_1 @ B ) =>
% 0.20/0.51           ( r1_tarski @
% 0.20/0.51             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.20/0.51             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X37 : $i, X38 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X37)
% 0.20/0.51          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X38 @ X37)) @ 
% 0.20/0.51             (k3_xboole_0 @ (k2_relat_1 @ X38) @ (k2_relat_1 @ X37)))
% 0.20/0.51          | ~ (v1_relat_1 @ X38))),
% 0.20/0.51      inference('cnf', [status(esa)], [t27_relat_1])).
% 0.20/0.51  thf(t63_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.51       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X8 @ X9)
% 0.20/0.51          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.20/0.51          | (r1_xboole_0 @ X8 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.20/0.51          | ~ (r1_xboole_0 @ 
% 0.20/0.51               (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.51          | (r1_xboole_0 @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.51  thf('9', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.51  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.51  thf('11', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (r1_xboole_0 @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0)),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '11', '12', '13'])).
% 0.20/0.51  thf(t66_xboole_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X13 : $i]: (((X13) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X13 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf(t64_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X39 : $i]:
% 0.20/0.51         (((k2_relat_1 @ X39) != (k1_xboole_0))
% 0.20/0.51          | ((X39) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X39))),
% 0.20/0.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.20/0.51        | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.51        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '19'])).
% 0.20/0.51  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.51  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
