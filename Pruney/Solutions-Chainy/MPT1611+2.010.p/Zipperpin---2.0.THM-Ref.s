%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OdKW7SRldG

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 (  77 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  317 ( 368 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(t19_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t19_yellow_1])).

thf('0',plain,(
    ( k4_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( k9_setfam_1 @ X7 )
      = ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X13 ) @ X13 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X13 ) )
        = ( k3_tarski @ X13 ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X13: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X13 ) )
        = ( k3_tarski @ X13 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X13 ) @ X13 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k3_yellow_1 @ X16 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('9',plain,(
    ! [X3: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('12',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k9_setfam_1 @ X7 )
      = ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ ( k2_struct_0 @ X0 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X4: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( k9_setfam_1 @ X7 )
      = ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('26',plain,(
    ! [X4: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_struct_0 @ X0 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','30'])).

thf('32',plain,(
    ! [X12: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','33'])).

thf('35',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OdKW7SRldG
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 41 iterations in 0.015s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.46  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.46  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.46  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.46  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.46  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.46  thf(t19_yellow_1, conjecture,
% 0.21/0.46    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.21/0.46  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t99_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.46  thf('1', plain, (![X3 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X3)) = (X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.46  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.46  thf('2', plain, (![X7 : $i]: ((k9_setfam_1 @ X7) = (k1_zfmisc_1 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('3', plain, (![X3 : $i]: ((k3_tarski @ (k9_setfam_1 @ X3)) = (X3))),
% 0.21/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf(t14_yellow_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.46       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.21/0.46         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X13 : $i]:
% 0.21/0.46         (~ (r2_hidden @ (k3_tarski @ X13) @ X13)
% 0.21/0.46          | ((k4_yellow_0 @ (k2_yellow_1 @ X13)) = (k3_tarski @ X13))
% 0.21/0.46          | (v1_xboole_0 @ X13))),
% 0.21/0.46      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.21/0.46  thf(d1_xboole_0, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X13 : $i]:
% 0.21/0.46         (((k4_yellow_0 @ (k2_yellow_1 @ X13)) = (k3_tarski @ X13))
% 0.21/0.46          | ~ (r2_hidden @ (k3_tarski @ X13) @ X13))),
% 0.21/0.46      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.46          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.21/0.46              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.46  thf(t4_yellow_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X16 : $i]: ((k3_yellow_1 @ X16) = (k2_yellow_1 @ (k9_setfam_1 @ X16)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.21/0.46  thf('9', plain, (![X3 : $i]: ((k3_tarski @ (k9_setfam_1 @ X3)) = (X3))),
% 0.21/0.46      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.46          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.46  thf(dt_l1_orders_2, axiom,
% 0.21/0.46    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.46  thf(d3_struct_0, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X8 : $i]:
% 0.21/0.46         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.46  thf(t1_yellow_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.46       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X14 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X14)) = (X14))),
% 0.21/0.46      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.21/0.46          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.46          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.46  thf(dt_k2_yellow_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.46       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.46  thf('17', plain, (![X12 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X12))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.46  thf('18', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf(dt_k2_struct_0, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( l1_struct_0 @ A ) =>
% 0.21/0.46       ( m1_subset_1 @
% 0.21/0.46         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (![X9 : $i]:
% 0.21/0.46         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.21/0.46           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.46          | ~ (l1_struct_0 @ X9))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.46  thf('20', plain, (![X7 : $i]: ((k9_setfam_1 @ X7) = (k1_zfmisc_1 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X9 : $i]:
% 0.21/0.46         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.21/0.46           (k9_setfam_1 @ (u1_struct_0 @ X9)))
% 0.21/0.46          | ~ (l1_struct_0 @ X9))),
% 0.21/0.46      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.46  thf(t2_subset, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]:
% 0.21/0.46         ((r2_hidden @ X5 @ X6)
% 0.21/0.46          | (v1_xboole_0 @ X6)
% 0.21/0.46          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (l1_struct_0 @ X0)
% 0.21/0.46          | (v1_xboole_0 @ (k9_setfam_1 @ (u1_struct_0 @ X0)))
% 0.21/0.46          | (r2_hidden @ (k2_struct_0 @ X0) @ 
% 0.21/0.46             (k9_setfam_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.46  thf(fc1_subset_1, axiom,
% 0.21/0.46    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.46  thf('24', plain, (![X4 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.46  thf('25', plain, (![X7 : $i]: ((k9_setfam_1 @ X7) = (k1_zfmisc_1 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('26', plain, (![X4 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X4))),
% 0.21/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r2_hidden @ (k2_struct_0 @ X0) @ (k9_setfam_1 @ (u1_struct_0 @ X0)))
% 0.21/0.46          | ~ (l1_struct_0 @ X0))),
% 0.21/0.46      inference('clc', [status(thm)], ['23', '26'])).
% 0.21/0.46  thf('28', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r2_hidden @ X0 @ (k9_setfam_1 @ (u1_struct_0 @ (k2_yellow_1 @ X0))))
% 0.21/0.46          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['18', '27'])).
% 0.21/0.46  thf('29', plain,
% 0.21/0.46      (![X14 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X14)) = (X14))),
% 0.21/0.46      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.46  thf('30', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.21/0.46          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.46  thf('31', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.46          | (r2_hidden @ X0 @ (k9_setfam_1 @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['11', '30'])).
% 0.21/0.46  thf('32', plain, (![X12 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X12))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.46  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.46  thf('34', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.21/0.46      inference('demod', [status(thm)], ['10', '33'])).
% 0.21/0.46  thf('35', plain, (((sk_A) != (sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '34'])).
% 0.21/0.46  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
