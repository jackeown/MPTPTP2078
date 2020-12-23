%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OoUQFc7YbJ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 110 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  401 ( 649 expanded)
%              Number of equality atoms :   27 (  32 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( X26 = X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( v1_xboole_0 @ X26 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference(clc,[status(thm)],['19','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_tarski @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','32'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('34',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('35',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X15: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    ! [X23: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference('sup-',[status(thm)],['33','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OoUQFc7YbJ
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:45:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 75 iterations in 0.046s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.51  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.51  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.22/0.51  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.22/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(t6_tex_2, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.51           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.51                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.51              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.51                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.22/0.51  thf('0', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ X19)
% 0.22/0.51          | ~ (m1_subset_1 @ X20 @ X19)
% 0.22/0.51          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.22/0.51        | (v1_xboole_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.22/0.51      inference('clc', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('6', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['0', '5'])).
% 0.22/0.51  thf('7', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_k6_domain_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.51       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X16 : $i, X17 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ X16)
% 0.22/0.51          | ~ (m1_subset_1 @ X17 @ X16)
% 0.22/0.51          | (m1_subset_1 @ (k6_domain_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.51        | (v1_xboole_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.22/0.51      inference('clc', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.51        | (v1_xboole_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('13', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf(t3_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i]:
% 0.22/0.51         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.51  thf('15', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.51  thf(t1_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.51           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X25 : $i, X26 : $i]:
% 0.22/0.51         ((v1_xboole_0 @ X25)
% 0.22/0.51          | ~ (v1_zfmisc_1 @ X25)
% 0.22/0.51          | ((X26) = (X25))
% 0.22/0.51          | ~ (r1_tarski @ X26 @ X25)
% 0.22/0.51          | (v1_xboole_0 @ X26))),
% 0.22/0.51      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.22/0.51        | ((k1_tarski @ sk_B) = (sk_A))
% 0.22/0.51        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.51        | (v1_xboole_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.22/0.51        | ((k1_tarski @ sk_B) = (sk_A))
% 0.22/0.51        | (v1_xboole_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.51  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.51  thf(t8_boole, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t8_boole])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.51  thf('23', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf(d1_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.51  thf('26', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.22/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.51  thf(t7_ordinal1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.51  thf('28', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.51  thf('29', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['24', '28'])).
% 0.22/0.51  thf('30', plain, (((v1_xboole_0 @ sk_A) | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.22/0.51      inference('clc', [status(thm)], ['19', '29'])).
% 0.22/0.51  thf('31', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('32', plain, (((k1_tarski @ sk_B) = (sk_A))),
% 0.22/0.51      inference('clc', [status(thm)], ['30', '31'])).
% 0.22/0.51  thf('33', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '32'])).
% 0.22/0.51  thf(dt_l1_orders_2, axiom,
% 0.22/0.51    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_orders_2 @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.51  thf(t1_yellow_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.22/0.51       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.22/0.51  thf(fc12_struct_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_struct_0 @ A ) =>
% 0.22/0.51       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X15 : $i]:
% 0.22/0.51         (~ (v1_subset_1 @ (k2_struct_0 @ X15) @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (l1_struct_0 @ X15))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.22/0.51          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_orders_2 @ X18))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.51  thf(d3_struct_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X14 : $i]:
% 0.22/0.51         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X23 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X23)) = (X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.22/0.51          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['39', '40'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.22/0.51          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '41'])).
% 0.22/0.51  thf(dt_k2_yellow_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.22/0.51       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.22/0.51  thf('43', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.22/0.51  thf('44', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['37', '44'])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['34', '45'])).
% 0.22/0.51  thf('47', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.22/0.51  thf('48', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.22/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('49', plain, ($false), inference('sup-', [status(thm)], ['33', '48'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
