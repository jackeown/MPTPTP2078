%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CdORSeP3ia

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:18 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   60 (  79 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  269 ( 412 expanded)
%              Number of equality atoms :   31 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( r2_hidden @ o_0_0_xboole_0 @ ( u1_pre_topc @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X25 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X25 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ o_0_0_xboole_0 @ X25 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X25 ) )
        = o_0_0_xboole_0 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

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

thf('8',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X8: $i] :
      ( ( X8 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( u1_pre_topc @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( r2_hidden @ o_0_0_xboole_0 @ ( u1_pre_topc @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('21',plain,
    ( ( r2_hidden @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ o_0_0_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X6 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k6_subset_1 @ o_0_0_xboole_0 @ X6 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X17 )
      | ~ ( r2_hidden @ X15 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ~ ( r2_hidden @ X17 @ ( k6_subset_1 @ X16 @ ( k1_tarski @ X17 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    $false ),
    inference('sup-',[status(thm)],['24','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CdORSeP3ia
% 0.16/0.38  % Computer   : n018.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:16:57 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 60 iterations in 0.025s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.23/0.52  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.23/0.52  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.23/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.52  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.23/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.23/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(t5_pre_topc, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.52       ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ))).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      (![X23 : $i]:
% 0.23/0.52         ((r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X23))
% 0.23/0.52          | ~ (l1_pre_topc @ X23)
% 0.23/0.52          | ~ (v2_pre_topc @ X23))),
% 0.23/0.52      inference('cnf', [status(esa)], [t5_pre_topc])).
% 0.23/0.52  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.23/0.52  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X23 : $i]:
% 0.23/0.52         ((r2_hidden @ o_0_0_xboole_0 @ (u1_pre_topc @ X23))
% 0.23/0.52          | ~ (l1_pre_topc @ X23)
% 0.23/0.52          | ~ (v2_pre_topc @ X23))),
% 0.23/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.52  thf(t13_yellow_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.52       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.23/0.52         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      (![X25 : $i]:
% 0.23/0.52         (~ (r2_hidden @ k1_xboole_0 @ X25)
% 0.23/0.52          | ((k3_yellow_0 @ (k2_yellow_1 @ X25)) = (k1_xboole_0))
% 0.23/0.52          | (v1_xboole_0 @ X25))),
% 0.23/0.52      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.23/0.52  thf('4', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.23/0.52  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      (![X25 : $i]:
% 0.23/0.52         (~ (r2_hidden @ o_0_0_xboole_0 @ X25)
% 0.23/0.52          | ((k3_yellow_0 @ (k2_yellow_1 @ X25)) = (o_0_0_xboole_0))
% 0.23/0.52          | (v1_xboole_0 @ X25))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (v2_pre_topc @ X0)
% 0.23/0.52          | ~ (l1_pre_topc @ X0)
% 0.23/0.52          | (v1_xboole_0 @ (u1_pre_topc @ X0))
% 0.23/0.52          | ((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.23/0.52              = (o_0_0_xboole_0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['2', '6'])).
% 0.23/0.52  thf(t23_yellow_1, conjecture,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.52       ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.23/0.52         ( k1_xboole_0 ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i]:
% 0.23/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.52            ( l1_pre_topc @ A ) ) =>
% 0.23/0.52          ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.23/0.52            ( k1_xboole_0 ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t23_yellow_1])).
% 0.23/0.52  thf('8', plain,
% 0.23/0.52      (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))) != (k1_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('9', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.23/0.52  thf('10', plain,
% 0.23/0.52      (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.23/0.52         != (o_0_0_xboole_0))),
% 0.23/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.23/0.52        | (v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 0.23/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.52        | ~ (v2_pre_topc @ sk_A))),
% 0.23/0.52      inference('sup-', [status(thm)], ['7', '10'])).
% 0.23/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.23/0.52        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.23/0.52  thf('15', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 0.23/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.23/0.52  thf(t6_boole, axiom,
% 0.23/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.23/0.52      inference('cnf', [status(esa)], [t6_boole])).
% 0.23/0.52  thf('17', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (![X8 : $i]: (((X8) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X8))),
% 0.23/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.52  thf('19', plain, (((u1_pre_topc @ sk_A) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['15', '18'])).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      (![X23 : $i]:
% 0.23/0.52         ((r2_hidden @ o_0_0_xboole_0 @ (u1_pre_topc @ X23))
% 0.23/0.52          | ~ (l1_pre_topc @ X23)
% 0.23/0.52          | ~ (v2_pre_topc @ X23))),
% 0.23/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.52  thf('21', plain,
% 0.23/0.52      (((r2_hidden @ o_0_0_xboole_0 @ o_0_0_xboole_0)
% 0.23/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.23/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.23/0.52  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('24', plain, ((r2_hidden @ o_0_0_xboole_0 @ o_0_0_xboole_0)),
% 0.23/0.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.23/0.52  thf(t4_boole, axiom,
% 0.23/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.52  thf('25', plain,
% 0.23/0.52      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.23/0.52  thf('26', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.23/0.52  thf('27', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.23/0.52  thf('28', plain,
% 0.23/0.52      (![X6 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X6) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.23/0.52  thf(redefinition_k6_subset_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.52  thf('29', plain,
% 0.23/0.52      (![X19 : $i, X20 : $i]:
% 0.23/0.52         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.52  thf('30', plain,
% 0.23/0.52      (![X6 : $i]: ((k6_subset_1 @ o_0_0_xboole_0 @ X6) = (o_0_0_xboole_0))),
% 0.23/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.52  thf(t64_zfmisc_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.23/0.52       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.23/0.52  thf('31', plain,
% 0.23/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.23/0.52         (((X15) != (X17))
% 0.23/0.52          | ~ (r2_hidden @ X15 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17))))),
% 0.23/0.52      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.23/0.52  thf('32', plain,
% 0.23/0.52      (![X16 : $i, X17 : $i]:
% 0.23/0.52         ~ (r2_hidden @ X17 @ (k4_xboole_0 @ X16 @ (k1_tarski @ X17)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.23/0.52  thf('33', plain,
% 0.23/0.52      (![X19 : $i, X20 : $i]:
% 0.23/0.52         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.23/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.23/0.52  thf('34', plain,
% 0.23/0.52      (![X16 : $i, X17 : $i]:
% 0.23/0.52         ~ (r2_hidden @ X17 @ (k6_subset_1 @ X16 @ (k1_tarski @ X17)))),
% 0.23/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.23/0.52  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.23/0.52      inference('sup-', [status(thm)], ['30', '34'])).
% 0.23/0.52  thf('36', plain, ($false), inference('sup-', [status(thm)], ['24', '35'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
