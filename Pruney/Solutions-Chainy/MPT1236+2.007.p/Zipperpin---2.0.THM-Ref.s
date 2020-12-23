%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2HuVyC7LQm

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 240 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( ( k1_struct_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( ( ( k1_struct_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf(fc8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_xboole_0 @ ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ ( k1_tops_1 @ X4 @ ( k1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc8_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X2: $i] :
      ( ( ( k1_struct_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

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

thf('11',plain,(
    ( k1_tops_1 @ sk_A @ ( k1_struct_0 @ sk_A ) )
 != ( k1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
     != ( k1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k1_tops_1 @ sk_A @ k1_xboole_0 )
 != ( k1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k1_xboole_0
     != ( k1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    k1_xboole_0
 != ( k1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('22',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2HuVyC7LQm
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:33:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 19 iterations in 0.018s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.48  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.22/0.48  thf(d2_struct_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X2 : $i]:
% 0.22/0.48         (((k1_struct_0 @ X2) = (k1_xboole_0)) | ~ (l1_struct_0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X2 : $i]:
% 0.22/0.48         (((k1_struct_0 @ X2) = (k1_xboole_0)) | ~ (l1_struct_0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.22/0.48  thf(fc8_tops_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( v1_xboole_0 @ ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X4 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k1_tops_1 @ X4 @ (k1_struct_0 @ X4)))
% 0.22/0.48          | ~ (l1_pre_topc @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc8_tops_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0))
% 0.22/0.48          | ~ (l1_struct_0 @ X0)
% 0.22/0.48          | ~ (l1_pre_topc @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf(dt_l1_pre_topc, axiom,
% 0.22/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.48  thf('4', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X0) | (v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.48      inference('clc', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.48  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.48  thf(t8_boole, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t8_boole])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X0)
% 0.22/0.48          | ((k1_xboole_0) = (k1_tops_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X2 : $i]:
% 0.22/0.48         (((k1_struct_0 @ X2) = (k1_xboole_0)) | ~ (l1_struct_0 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.22/0.48  thf(t47_tops_1, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( l1_pre_topc @ A ) =>
% 0.22/0.48          ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t47_tops_1])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (((k1_tops_1 @ sk_A @ (k1_struct_0 @ sk_A)) != (k1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      ((((k1_tops_1 @ sk_A @ k1_xboole_0) != (k1_struct_0 @ sk_A))
% 0.22/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('14', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.48  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (((k1_tops_1 @ sk_A @ k1_xboole_0) != (k1_struct_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['12', '15'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      ((((k1_xboole_0) != (k1_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '16'])).
% 0.22/0.48  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('19', plain, (((k1_xboole_0) != (k1_struct_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '19'])).
% 0.22/0.48  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('22', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
