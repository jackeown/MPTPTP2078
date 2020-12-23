%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dqf8GYnZqq

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t4_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
        = ( k9_setfam_1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t4_waybel_7])).

thf('0',plain,(
    ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) )
 != ( k9_setfam_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k3_yellow_1 @ X2 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X0 ) )
      = ( k9_setfam_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k9_setfam_1 @ sk_A )
 != ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dqf8GYnZqq
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 4 iterations in 0.007s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.20/0.46  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.46  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.20/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.46  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.46  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(t4_waybel_7, conjecture,
% 0.20/0.46    (![A:$i]: ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) = ( k9_setfam_1 @ A ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) = ( k9_setfam_1 @ A ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t4_waybel_7])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((u1_struct_0 @ (k3_yellow_1 @ sk_A)) != (k9_setfam_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t4_yellow_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X2 : $i]: ((k3_yellow_1 @ X2) = (k2_yellow_1 @ (k9_setfam_1 @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.20/0.46  thf(t1_yellow_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.20/0.46       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.46  thf('2', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X0)) = (k9_setfam_1 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain, (((k9_setfam_1 @ sk_A) != (k9_setfam_1 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.46  thf('5', plain, ($false), inference('simplify', [status(thm)], ['4'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
