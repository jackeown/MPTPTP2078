%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CHYSty0uPd

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 131 expanded)
%              Number of leaves         :   41 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  495 ( 766 expanded)
%              Number of equality atoms :   43 (  50 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( v1_zfmisc_1 @ X28 )
      | ( X29 = X28 )
      | ~ ( r1_tarski @ X29 @ X28 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('23',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_subset_1 @ sk_A @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('26',plain,(
    ! [X13: $i] :
      ( v1_xboole_0 @ ( sk_B @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['24','43'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('45',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('46',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X18: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('50',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    ! [X26: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('59',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference('sup-',[status(thm)],['44','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CHYSty0uPd
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 58 iterations in 0.024s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.48  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(t6_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.48           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.48                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.48              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.48                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.21/0.48  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k6_domain_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.48       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X19 : $i, X20 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X19)
% 0.21/0.48          | ~ (m1_subset_1 @ X20 @ X19)
% 0.21/0.48          | (m1_subset_1 @ (k6_domain_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X22)
% 0.21/0.48          | ~ (m1_subset_1 @ X23 @ X22)
% 0.21/0.48          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '7'])).
% 0.21/0.48  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf(t3_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.48  thf('12', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf(t1_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.21/0.48           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X28 : $i, X29 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X28)
% 0.21/0.48          | ~ (v1_zfmisc_1 @ X28)
% 0.21/0.48          | ((X29) = (X28))
% 0.21/0.48          | ~ (r1_tarski @ X29 @ X28)
% 0.21/0.48          | (v1_xboole_0 @ X29))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.21/0.48        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.21/0.48        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.21/0.48        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((((k1_tarski @ sk_B_1) = (sk_A)) | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.21/0.48      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf(l13_xboole_0, axiom,
% 0.21/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((k1_tarski @ sk_B_1) = (sk_A))
% 0.21/0.48        | ((k1_tarski @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('23', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((v1_subset_1 @ sk_A @ sk_A) | ((k1_tarski @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['20', '23'])).
% 0.21/0.48  thf(rc2_subset_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ?[B:$i]:
% 0.21/0.48       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X13 : $i]: (m1_subset_1 @ (sk_B @ X13) @ (k1_zfmisc_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.48  thf('26', plain, (![X13 : $i]: (v1_xboole_0 @ (sk_B @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.48  thf('28', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.48  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf(t28_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf(t100_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ X1 @ X2)
% 0.21/0.48           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.48           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf(t5_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.48  thf('36', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf(t98_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ X6 @ X7)
% 0.21/0.48           = (k5_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.48  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.48  thf(t49_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.48  thf('43', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('44', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['24', '43'])).
% 0.21/0.48  thf(dt_l1_orders_2, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_orders_2 @ X21))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.48  thf(t1_yellow_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.48       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.48  thf(fc12_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) =>
% 0.21/0.48       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X18 : $i]:
% 0.21/0.48         (~ (v1_subset_1 @ (k2_struct_0 @ X18) @ (u1_struct_0 @ X18))
% 0.21/0.48          | ~ (l1_struct_0 @ X18))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.21/0.48          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_orders_2 @ X21))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.48  thf(d3_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (![X17 : $i]:
% 0.21/0.48         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (![X26 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X26)) = (X26))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.21/0.48          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['50', '51'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.48          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['49', '52'])).
% 0.21/0.48  thf(dt_k2_yellow_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.48       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.48  thf('54', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.48  thf('55', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['48', '55'])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['45', '56'])).
% 0.21/0.48  thf('58', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.48  thf('59', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.21/0.48      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.48  thf('60', plain, ($false), inference('sup-', [status(thm)], ['44', '59'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
