%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wi10pT5woV

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:53 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 149 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  513 (1921 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t50_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ~ ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( ( k6_domain_1 @ X25 @ X26 )
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_B_1 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_B_1 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
            & ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X28 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X28 ) @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_orders_2 @ X28 )
      | ~ ( v3_orders_2 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(dt_k2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_orders_2])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X18 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t49_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( r2_hidden @ B @ C )
                  & ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r2_hidden @ X29 @ ( k2_orders_2 @ X30 @ X31 ) )
      | ~ ( r2_hidden @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_orders_2 @ X30 )
      | ~ ( v5_orders_2 @ X30 )
      | ~ ( v4_orders_2 @ X30 )
      | ~ ( v3_orders_2 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t49_orders_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('39',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','39'])).

thf('41',plain,(
    r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['40','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wi10pT5woV
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 174 iterations in 0.116s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.39/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.39/0.58  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.39/0.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.39/0.58  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.39/0.58  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(t50_orders_2, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.58           ( ~( r2_hidden @
% 0.39/0.58                B @ 
% 0.39/0.58                ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.58            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.58              ( ~( r2_hidden @
% 0.39/0.58                   B @ 
% 0.39/0.58                   ( k2_orders_2 @
% 0.39/0.58                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t50_orders_2])).
% 0.39/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X25 : $i, X26 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ X25)
% 0.39/0.58          | ~ (m1_subset_1 @ X26 @ X25)
% 0.39/0.58          | ((k6_domain_1 @ X25 @ X26) = (k1_tarski @ X26)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      ((r2_hidden @ sk_B_1 @ 
% 0.39/0.58        (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (((r2_hidden @ sk_B_1 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      ((r2_hidden @ sk_B_1 @ 
% 0.39/0.58        (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t35_orders_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.58           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.39/0.58             ( m1_subset_1 @
% 0.39/0.58               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.39/0.58               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X27 : $i, X28 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X28))
% 0.39/0.58          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X28) @ X27) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.39/0.58          | ~ (l1_orders_2 @ X28)
% 0.39/0.58          | ~ (v3_orders_2 @ X28)
% 0.39/0.58          | (v2_struct_0 @ X28))),
% 0.39/0.58      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | ~ (v3_orders_2 @ sk_A)
% 0.39/0.58        | ~ (l1_orders_2 @ sk_A)
% 0.39/0.58        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('10', plain, ((v3_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_A)
% 0.39/0.58        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.39/0.58  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('clc', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf(dt_k2_orders_2, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.39/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.58       ( m1_subset_1 @
% 0.39/0.58         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X23 : $i, X24 : $i]:
% 0.39/0.58         (~ (l1_orders_2 @ X23)
% 0.39/0.58          | ~ (v5_orders_2 @ X23)
% 0.39/0.58          | ~ (v4_orders_2 @ X23)
% 0.39/0.58          | ~ (v3_orders_2 @ X23)
% 0.39/0.58          | (v2_struct_0 @ X23)
% 0.39/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.39/0.58          | (m1_subset_1 @ (k2_orders_2 @ X23 @ X24) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (((m1_subset_1 @ 
% 0.39/0.58         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58        | (v2_struct_0 @ sk_A)
% 0.39/0.58        | ~ (v3_orders_2 @ sk_A)
% 0.39/0.58        | ~ (v4_orders_2 @ sk_A)
% 0.39/0.58        | ~ (v5_orders_2 @ sk_A)
% 0.39/0.58        | ~ (l1_orders_2 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('17', plain, ((v3_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('18', plain, ((v4_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('19', plain, ((v5_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('20', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (((m1_subset_1 @ 
% 0.39/0.58         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.58        | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.39/0.58  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      ((m1_subset_1 @ 
% 0.39/0.58        (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('clc', [status(thm)], ['21', '22'])).
% 0.39/0.58  thf(l3_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X15 @ X16)
% 0.39/0.58          | (r2_hidden @ X15 @ X17)
% 0.39/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.39/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ 
% 0.39/0.58               (k2_orders_2 @ sk_A @ 
% 0.39/0.58                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.58  thf('26', plain, ((r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '25'])).
% 0.39/0.58  thf(t63_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.58       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i]:
% 0.39/0.58         ((m1_subset_1 @ (k1_tarski @ X18) @ (k1_zfmisc_1 @ X19))
% 0.39/0.58          | ~ (r2_hidden @ X18 @ X19))),
% 0.39/0.58      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      ((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf(t49_orders_2, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.39/0.58         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58               ( ~( ( r2_hidden @ B @ C ) & 
% 0.39/0.58                    ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.39/0.58          | ~ (r2_hidden @ X29 @ (k2_orders_2 @ X30 @ X31))
% 0.39/0.58          | ~ (r2_hidden @ X29 @ X31)
% 0.39/0.58          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.39/0.58          | ~ (l1_orders_2 @ X30)
% 0.39/0.58          | ~ (v5_orders_2 @ X30)
% 0.39/0.58          | ~ (v4_orders_2 @ X30)
% 0.39/0.58          | ~ (v3_orders_2 @ X30)
% 0.39/0.58          | (v2_struct_0 @ X30))),
% 0.39/0.58      inference('cnf', [status(esa)], [t49_orders_2])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_A)
% 0.39/0.58          | ~ (v3_orders_2 @ sk_A)
% 0.39/0.58          | ~ (v4_orders_2 @ sk_A)
% 0.39/0.58          | ~ (v5_orders_2 @ sk_A)
% 0.39/0.58          | ~ (l1_orders_2 @ sk_A)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B_1))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf('31', plain, ((v3_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('32', plain, ((v4_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('33', plain, ((v5_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_struct_0 @ sk_A)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B_1))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ~ (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_B_1))
% 0.39/0.58        | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '35'])).
% 0.39/0.58  thf('37', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d1_tarski, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.58         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.58  thf('39', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.39/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['36', '37', '39'])).
% 0.39/0.58  thf('41', plain, ((r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '25'])).
% 0.39/0.58  thf(d1_xboole_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('43', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf('44', plain, ((v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('clc', [status(thm)], ['40', '43'])).
% 0.39/0.58  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
