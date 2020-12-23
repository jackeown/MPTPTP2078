%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gx0z66f5Ze

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 111 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  412 ( 743 expanded)
%              Number of equality atoms :   34 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
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
    ( ( ( k6_domain_1 @ sk_A @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( ~ ( v1_zfmisc_1 @ X19 )
      | ( X19
        = ( k6_domain_1 @ X19 @ ( sk_B_1 @ X19 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('13',plain,(
    ! [X19: $i] :
      ( ~ ( v1_zfmisc_1 @ X19 )
      | ( m1_subset_1 @ ( sk_B_1 @ X19 ) @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1
        = ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( sk_B_2
      = ( sk_B_1 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B_2
      = ( sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( sk_B_2
    = ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X19: $i] :
      ( ~ ( v1_zfmisc_1 @ X19 )
      | ( X19
        = ( k6_domain_1 @ X19 @ ( sk_B_1 @ X19 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('28',plain,
    ( ( sk_A
      = ( k6_domain_1 @ sk_A @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_2 )
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('30',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_2 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','33'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('35',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('36',plain,(
    ! [X17: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('37',plain,(
    ! [X11: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('40',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,(
    ! [X17: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sup-',[status(thm)],['34','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gx0z66f5Ze
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:40:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 77 iterations in 0.040s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.22/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.22/0.50  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.22/0.50  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.22/0.50  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(t6_tex_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.50           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.50                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.50              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.50                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.22/0.50  thf('0', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_2) @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X13)
% 0.22/0.50          | ~ (m1_subset_1 @ X14 @ X13)
% 0.22/0.50          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.22/0.50        | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.22/0.50      inference('clc', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_2) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '5'])).
% 0.22/0.50  thf('7', plain, ((m1_subset_1 @ sk_B_2 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t2_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         ((r2_hidden @ X8 @ X9)
% 0.22/0.50          | (v1_xboole_0 @ X9)
% 0.22/0.50          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.50  thf('9', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_2 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain, ((r2_hidden @ sk_B_2 @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf(d1_tex_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50       ( ( v1_zfmisc_1 @ A ) <=>
% 0.22/0.50         ( ?[B:$i]:
% 0.22/0.50           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X19 : $i]:
% 0.22/0.50         (~ (v1_zfmisc_1 @ X19)
% 0.22/0.50          | ((X19) = (k6_domain_1 @ X19 @ (sk_B_1 @ X19)))
% 0.22/0.50          | (v1_xboole_0 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X19 : $i]:
% 0.22/0.50         (~ (v1_zfmisc_1 @ X19)
% 0.22/0.50          | (m1_subset_1 @ (sk_B_1 @ X19) @ X19)
% 0.22/0.50          | (v1_xboole_0 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X13)
% 0.22/0.50          | ~ (m1_subset_1 @ X14 @ X13)
% 0.22/0.50          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.22/0.50          | (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.22/0.50          | (v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | (v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['12', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | (v1_xboole_0 @ X0)
% 0.22/0.50          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.50  thf(d1_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X3 : $i, X6 : $i]:
% 0.22/0.50         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ X0)
% 0.22/0.50          | (v1_xboole_0 @ X0)
% 0.22/0.50          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.50          | ((X1) = (sk_B_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      ((((sk_B_2) = (sk_B_1 @ sk_A))
% 0.22/0.50        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.50        | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '21'])).
% 0.22/0.50  thf('23', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain, ((((sk_B_2) = (sk_B_1 @ sk_A)) | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('26', plain, (((sk_B_2) = (sk_B_1 @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X19 : $i]:
% 0.22/0.50         (~ (v1_zfmisc_1 @ X19)
% 0.22/0.50          | ((X19) = (k6_domain_1 @ X19 @ (sk_B_1 @ X19)))
% 0.22/0.50          | (v1_xboole_0 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((((sk_A) = (k6_domain_1 @ sk_A @ sk_B_2))
% 0.22/0.50        | (v1_xboole_0 @ sk_A)
% 0.22/0.50        | ~ (v1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain, (((k6_domain_1 @ sk_A @ sk_B_2) = (k1_tarski @ sk_B_2))),
% 0.22/0.50      inference('clc', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('30', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('31', plain, ((((sk_A) = (k1_tarski @ sk_B_2)) | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.22/0.50  thf('32', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('33', plain, (((sk_A) = (k1_tarski @ sk_B_2))),
% 0.22/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.22/0.50  thf('34', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['6', '33'])).
% 0.22/0.50  thf(dt_l1_orders_2, axiom,
% 0.22/0.50    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_orders_2 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.50  thf(t1_yellow_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.22/0.50       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X17 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X17)) = (X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.22/0.50  thf(fc12_struct_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_struct_0 @ A ) =>
% 0.22/0.50       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X11 : $i]:
% 0.22/0.50         (~ (v1_subset_1 @ (k2_struct_0 @ X11) @ (u1_struct_0 @ X11))
% 0.22/0.50          | ~ (l1_struct_0 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.22/0.50          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_orders_2 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.50  thf(d3_struct_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X10 : $i]:
% 0.22/0.50         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X17 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X17)) = (X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.22/0.50          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.22/0.50          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.50  thf(dt_k2_yellow_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.22/0.50       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.22/0.50  thf('44', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.22/0.50  thf('45', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '45'])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '46'])).
% 0.22/0.50  thf('48', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.22/0.50  thf('49', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.22/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.50  thf('50', plain, ($false), inference('sup-', [status(thm)], ['34', '49'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
