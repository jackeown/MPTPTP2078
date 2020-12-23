%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.onOm11mtI8

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  167 ( 271 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X4 ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X5 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X5 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t23_yellow_1])).

thf('3',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X4 ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_pre_topc @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['16','17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.onOm11mtI8
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 14 iterations in 0.012s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.44  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.44  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.44  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.20/0.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.44  thf(t5_pre_topc, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.44       ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ))).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (![X4 : $i]:
% 0.20/0.44         ((r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X4))
% 0.20/0.44          | ~ (l1_pre_topc @ X4)
% 0.20/0.44          | ~ (v2_pre_topc @ X4))),
% 0.20/0.44      inference('cnf', [status(esa)], [t5_pre_topc])).
% 0.20/0.44  thf(t13_yellow_1, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.44       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.44         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (![X5 : $i]:
% 0.20/0.44         (~ (r2_hidden @ k1_xboole_0 @ X5)
% 0.20/0.44          | ((k3_yellow_0 @ (k2_yellow_1 @ X5)) = (k1_xboole_0))
% 0.20/0.44          | (v1_xboole_0 @ X5))),
% 0.20/0.44      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (~ (v2_pre_topc @ X0)
% 0.20/0.44          | ~ (l1_pre_topc @ X0)
% 0.20/0.44          | (v1_xboole_0 @ (u1_pre_topc @ X0))
% 0.20/0.44          | ((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0))) = (k1_xboole_0)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.44  thf(t23_yellow_1, conjecture,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.44       ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.44         ( k1_xboole_0 ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i]:
% 0.20/0.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.44            ( l1_pre_topc @ A ) ) =>
% 0.20/0.44          ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.44            ( k1_xboole_0 ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t23_yellow_1])).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))) != (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.44        | (v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 0.20/0.44        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.44        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.44  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      ((((k1_xboole_0) != (k1_xboole_0)) | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 0.20/0.44      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.44  thf('8', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 0.20/0.44      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.44  thf(l13_xboole_0, axiom,
% 0.20/0.44    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.44      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.44  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.44  thf('10', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.20/0.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      (![X4 : $i]:
% 0.20/0.44         ((r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X4))
% 0.20/0.44          | ~ (l1_pre_topc @ X4)
% 0.20/0.44          | ~ (v2_pre_topc @ X4))),
% 0.20/0.44      inference('cnf', [status(esa)], [t5_pre_topc])).
% 0.20/0.44  thf(t7_ordinal1, axiom,
% 0.20/0.44    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.44  thf('13', plain,
% 0.20/0.44      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (~ (v2_pre_topc @ X0)
% 0.20/0.44          | ~ (l1_pre_topc @ X0)
% 0.20/0.44          | ~ (r1_tarski @ (u1_pre_topc @ X0) @ k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (~ (v1_xboole_0 @ (u1_pre_topc @ X0))
% 0.20/0.44          | ~ (l1_pre_topc @ X0)
% 0.20/0.44          | ~ (v2_pre_topc @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.44  thf('16', plain, ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['8', '15'])).
% 0.20/0.44  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('19', plain, ($false),
% 0.20/0.44      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
