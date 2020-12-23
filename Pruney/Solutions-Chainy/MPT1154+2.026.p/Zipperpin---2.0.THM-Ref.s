%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1mkFBNbry6

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 113 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   17
%              Number of atoms          :  450 (1137 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t48_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( ( k6_domain_1 @ X9 @ X10 )
        = ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,
    ( ( ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t47_orders_2,axiom,(
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
                  & ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_orders_2 @ X14 @ X15 ) )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_orders_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','34'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k1_tarski @ X2 ) )
      | ( X1
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('37',plain,(
    ! [X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k1_tarski @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','39'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('41',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('44',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1mkFBNbry6
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:08:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 76 iterations in 0.037s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.50  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.21/0.50  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.50  thf(t48_orders_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ~( r2_hidden @
% 0.21/0.50                B @ 
% 0.21/0.50                ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.50            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50              ( ~( r2_hidden @
% 0.21/0.50                   B @ 
% 0.21/0.50                   ( k1_orders_2 @
% 0.21/0.50                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t48_orders_2])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X6 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_B @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l1_orders_2, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('5', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_orders_2 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.50  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, ((m1_subset_1 @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X9)
% 0.21/0.50          | ~ (m1_subset_1 @ X10 @ X9)
% 0.21/0.50          | ((k6_domain_1 @ X9 @ X10) = (k1_tarski @ X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((((k6_domain_1 @ (k2_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.50        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X6 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((r2_hidden @ sk_B @ 
% 0.21/0.50        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t35_orders_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.21/0.50             ( m1_subset_1 @
% 0.21/0.50               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.50               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.21/0.50          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X12) @ X11) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.50          | ~ (l1_orders_2 @ X12)
% 0.21/0.50          | ~ (v3_orders_2 @ X12)
% 0.21/0.50          | (v2_struct_0 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.50        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.50        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.50  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf(t47_orders_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.50         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50               ( ~( ( r2_hidden @ B @ C ) & 
% 0.21/0.50                    ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.21/0.50          | ~ (r2_hidden @ X13 @ (k1_orders_2 @ X14 @ X15))
% 0.21/0.50          | ~ (r2_hidden @ X13 @ X15)
% 0.21/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.50          | ~ (l1_orders_2 @ X14)
% 0.21/0.50          | ~ (v5_orders_2 @ X14)
% 0.21/0.50          | ~ (v4_orders_2 @ X14)
% 0.21/0.50          | ~ (v3_orders_2 @ X14)
% 0.21/0.50          | (v2_struct_0 @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t47_orders_2])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.50          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.50          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.50          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ 
% 0.21/0.50               (k1_orders_2 @ sk_A @ 
% 0.21/0.50                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ 
% 0.21/0.50               (k1_orders_2 @ sk_A @ 
% 0.21/0.50                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '26'])).
% 0.21/0.50  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_B @ (k6_domain_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '31'])).
% 0.21/0.50  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (~ (r2_hidden @ sk_B @ (k6_domain_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.21/0.50        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '34'])).
% 0.21/0.50  thf(l3_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ (k1_tarski @ X2)) | ((X1) != (k1_tarski @ X2)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X2 : $i]: (r1_tarski @ (k1_tarski @ X2) @ (k1_tarski @ X2))),
% 0.21/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.50  thf(t37_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         ((r2_hidden @ X3 @ X4) | ~ (r1_tarski @ (k1_tarski @ X3) @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.21/0.50  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '39'])).
% 0.21/0.50  thf(fc5_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (k2_struct_0 @ X7))
% 0.21/0.50          | ~ (l1_struct_0 @ X7)
% 0.21/0.50          | (v2_struct_0 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.21/0.50  thf('42', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('44', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.50  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
