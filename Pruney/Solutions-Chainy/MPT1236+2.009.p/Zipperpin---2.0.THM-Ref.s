%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qae0KTwtPT

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 138 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( ( k1_struct_0 @ X1 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf(fc8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_xboole_0 @ ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k1_tops_1 @ X3 @ ( k1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc8_tops_1])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t47_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) )
        = ( k1_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) )
          = ( k1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_tops_1])).

thf('4',plain,(
    ( k1_tops_1 @ sk_A @ ( k1_struct_0 @ sk_A ) )
 != ( k1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_xboole_0
     != ( k1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    k1_xboole_0
 != ( k1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qae0KTwtPT
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:52:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 9 iterations in 0.010s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.45  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.45  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.19/0.45  thf(d2_struct_0, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      (![X1 : $i]:
% 0.19/0.45         (((k1_struct_0 @ X1) = (k1_xboole_0)) | ~ (l1_struct_0 @ X1))),
% 0.19/0.45      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.19/0.45  thf(fc8_tops_1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( l1_pre_topc @ A ) =>
% 0.19/0.45       ( v1_xboole_0 @ ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X3 : $i]:
% 0.19/0.46         ((v1_xboole_0 @ (k1_tops_1 @ X3 @ (k1_struct_0 @ X3)))
% 0.19/0.46          | ~ (l1_pre_topc @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc8_tops_1])).
% 0.19/0.46  thf(t6_boole, axiom,
% 0.19/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t6_boole])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (l1_pre_topc @ X0)
% 0.19/0.46          | ((k1_tops_1 @ X0 @ (k1_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t47_tops_1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( l1_pre_topc @ A ) =>
% 0.19/0.46       ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( l1_pre_topc @ A ) =>
% 0.19/0.46          ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t47_tops_1])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (((k1_tops_1 @ sk_A @ (k1_struct_0 @ sk_A)) != (k1_struct_0 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      ((((k1_xboole_0) != (k1_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('7', plain, (((k1_xboole_0) != (k1_struct_0 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '7'])).
% 0.19/0.46  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(dt_l1_pre_topc, axiom,
% 0.19/0.46    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.46  thf('10', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.46  thf('11', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf('12', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['8', '11'])).
% 0.19/0.46  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
