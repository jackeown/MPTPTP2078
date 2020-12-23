%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CA3bw1zW8X

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  35 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   86 ( 158 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v8_struct_0_type,type,(
    v8_struct_0: $i > $o )).

thf(t27_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_finset_1 @ ( u1_struct_0 @ A ) )
       => ( v1_compts_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( v1_finset_1 @ ( u1_struct_0 @ A ) )
         => ( v1_compts_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_compts_1])).

thf('0',plain,(
    ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ( v8_struct_0 @ A )
          & ( v2_pre_topc @ A ) )
       => ( ( v2_pre_topc @ A )
          & ( v1_compts_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ~ ( v8_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v1_compts_1 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc3_compts_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ~ ( v8_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_finset_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v8_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_finset_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ~ ( v1_finset_1 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v8_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc9_struct_0])).

thf('7',plain,
    ( ( v8_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v8_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    v1_compts_1 @ sk_A ),
    inference(demod,[status(thm)],['3','4','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CA3bw1zW8X
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:19 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 10 iterations in 0.008s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(v8_struct_0_type, type, v8_struct_0: $i > $o).
% 0.20/0.47  thf(t27_compts_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ( v1_finset_1 @ ( u1_struct_0 @ A ) ) => ( v1_compts_1 @ A ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ( v1_finset_1 @ ( u1_struct_0 @ A ) ) => ( v1_compts_1 @ A ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t27_compts_1])).
% 0.20/0.47  thf('0', plain, (~ (v1_compts_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc3_compts_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ( ( v8_struct_0 @ A ) & ( v2_pre_topc @ A ) ) =>
% 0.20/0.47         ( ( v2_pre_topc @ A ) & ( v1_compts_1 @ A ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X2 : $i]:
% 0.20/0.47         (~ (v8_struct_0 @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X2)
% 0.20/0.47          | (v1_compts_1 @ X2)
% 0.20/0.47          | ~ (l1_pre_topc @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc3_compts_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_A) | (v1_compts_1 @ sk_A) | ~ (v8_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, ((v1_finset_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(fc9_struct_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v8_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( ~( v1_finset_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X1 : $i]:
% 0.20/0.47         (~ (v1_finset_1 @ (u1_struct_0 @ X1))
% 0.20/0.47          | ~ (l1_struct_0 @ X1)
% 0.20/0.47          | (v8_struct_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc9_struct_0])).
% 0.20/0.47  thf('7', plain, (((v8_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_l1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.47  thf('9', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.47  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain, ((v8_struct_0 @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.47  thf('12', plain, ((v1_compts_1 @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4', '11'])).
% 0.20/0.47  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
