%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kNIeIbVPT7

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 107 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  383 ( 631 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('15',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_zfmisc_1 @ X19 )
      | ( X20 = X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference(clc,[status(thm)],['19','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','30'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('32',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('33',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('34',plain,(
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

thf('35',plain,(
    ! [X17: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('40',plain,(
    ! [X9: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sup-',[status(thm)],['31','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kNIeIbVPT7
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:19:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 61 iterations in 0.035s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.49  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(t6_tex_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.49           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.49                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.49              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.49                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.21/0.49  thf('0', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.49       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X13)
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ X13)
% 0.21/0.49          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.49        | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.49  thf('7', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k6_domain_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X11 @ X10)
% 0.21/0.49          | (m1_subset_1 @ (k6_domain_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.49        | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('13', plain, ((r1_tarski @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('15', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf(t1_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.49           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X19)
% 0.21/0.49          | ~ (v1_zfmisc_1 @ X19)
% 0.21/0.49          | ((X20) = (X19))
% 0.21/0.49          | ~ (r1_tarski @ X20 @ X19)
% 0.21/0.49          | (v1_xboole_0 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.21/0.49        | ((k1_tarski @ sk_B) = (sk_A))
% 0.21/0.49        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.49        | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.21/0.49        | ((k1_tarski @ sk_B) = (sk_A))
% 0.21/0.49        | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf(t8_boole, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_boole])).
% 0.21/0.49  thf(t1_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.49  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.49  thf(t49_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.49  thf('23', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X0) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_xboole_0 @ X0)
% 0.21/0.49          | ~ (v1_xboole_0 @ (k1_tarski @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X1 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (k1_tarski @ X1)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.49  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.49  thf('27', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X1))),
% 0.21/0.49      inference('simplify_reflect+', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain, (((v1_xboole_0 @ sk_A) | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['19', '27'])).
% 0.21/0.49  thf('29', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain, (((k1_tarski @ sk_B) = (sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '30'])).
% 0.21/0.49  thf(dt_l1_orders_2, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_orders_2 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_orders_2 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.49  thf(d3_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X8 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf(t1_yellow_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.49       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X17 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X17)) = (X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.21/0.49          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.49          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.49  thf(dt_k2_yellow_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.49       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.49  thf('38', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.49  thf('39', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf(fc12_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) =>
% 0.21/0.49       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X9 : $i]:
% 0.21/0.49         (~ (v1_subset_1 @ (k2_struct_0 @ X9) @ (u1_struct_0 @ X9))
% 0.21/0.49          | ~ (l1_struct_0 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.21/0.49          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X17 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X17)) = (X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '43'])).
% 0.21/0.49  thf('45', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.49  thf('46', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain, ($false), inference('sup-', [status(thm)], ['31', '46'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
