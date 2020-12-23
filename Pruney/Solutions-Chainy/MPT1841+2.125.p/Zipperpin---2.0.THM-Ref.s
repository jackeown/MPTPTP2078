%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Du5IBaqvS

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:45 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 162 expanded)
%              Number of leaves         :   46 (  67 expanded)
%              Depth                    :   21
%              Number of atoms          :  608 (1067 expanded)
%              Number of equality atoms :   58 (  69 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( ( k6_domain_1 @ X39 @ X40 )
        = ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf(t2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) )
         => ( r1_tarski @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X45: $i,X46: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X45 @ X46 ) )
      | ( r1_tarski @ X45 @ X46 )
      | ~ ( v1_zfmisc_1 @ X45 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t2_tex_2])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X19 )
      | ( ( k4_xboole_0 @ X17 @ X19 )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_B_1 )
     != ( k1_tarski @ sk_B_1 ) )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('40',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('46',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','48'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('50',plain,(
    ! [X38: $i] :
      ( ( l1_struct_0 @ X38 )
      | ~ ( l1_orders_2 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('51',plain,(
    ! [X43: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('52',plain,(
    ! [X35: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X35 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X38: $i] :
      ( ( l1_struct_0 @ X38 )
      | ~ ( l1_orders_2 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('55',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    ! [X43: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X42: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,(
    ! [X42: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('sup-',[status(thm)],['49','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Du5IBaqvS
% 0.15/0.37  % Computer   : n011.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 15:45:12 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.46/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.62  % Solved by: fo/fo7.sh
% 0.46/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.62  % done 304 iterations in 0.133s
% 0.46/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.62  % SZS output start Refutation
% 0.46/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.62  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.46/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.62  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.46/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.62  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.46/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.62  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.46/0.62  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.46/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.62  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.46/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.62  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.46/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.62  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.46/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.62  thf(t6_tex_2, conjecture,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.62       ( ![B:$i]:
% 0.46/0.62         ( ( m1_subset_1 @ B @ A ) =>
% 0.46/0.62           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.46/0.62                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.46/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.62    (~( ![A:$i]:
% 0.46/0.62        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.62          ( ![B:$i]:
% 0.46/0.62            ( ( m1_subset_1 @ B @ A ) =>
% 0.46/0.62              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.46/0.62                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.46/0.62    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.46/0.62  thf('0', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf(redefinition_k6_domain_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.62       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.46/0.62  thf('2', plain,
% 0.46/0.62      (![X39 : $i, X40 : $i]:
% 0.46/0.62         ((v1_xboole_0 @ X39)
% 0.46/0.62          | ~ (m1_subset_1 @ X40 @ X39)
% 0.46/0.62          | ((k6_domain_1 @ X39 @ X40) = (k1_tarski @ X40)))),
% 0.46/0.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.62  thf('3', plain,
% 0.46/0.62      ((((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.46/0.62        | (v1_xboole_0 @ sk_A))),
% 0.46/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.62  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.46/0.62      inference('clc', [status(thm)], ['3', '4'])).
% 0.46/0.62  thf('6', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.46/0.62      inference('demod', [status(thm)], ['0', '5'])).
% 0.46/0.62  thf(t2_tex_2, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.46/0.62       ( ![B:$i]:
% 0.46/0.62         ( ( ~( v1_xboole_0 @ ( k3_xboole_0 @ A @ B ) ) ) =>
% 0.46/0.62           ( r1_tarski @ A @ B ) ) ) ))).
% 0.46/0.62  thf('7', plain,
% 0.46/0.62      (![X45 : $i, X46 : $i]:
% 0.46/0.62         ((v1_xboole_0 @ (k3_xboole_0 @ X45 @ X46))
% 0.46/0.62          | (r1_tarski @ X45 @ X46)
% 0.46/0.62          | ~ (v1_zfmisc_1 @ X45)
% 0.46/0.62          | (v1_xboole_0 @ X45))),
% 0.46/0.62      inference('cnf', [status(esa)], [t2_tex_2])).
% 0.46/0.62  thf(l13_xboole_0, axiom,
% 0.46/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.62  thf('8', plain,
% 0.46/0.62      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.46/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.62  thf('9', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         ((v1_xboole_0 @ X1)
% 0.46/0.62          | ~ (v1_zfmisc_1 @ X1)
% 0.46/0.62          | (r1_tarski @ X1 @ X0)
% 0.46/0.62          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.62  thf('10', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf(dt_k6_domain_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.62       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.62  thf('11', plain,
% 0.46/0.62      (![X36 : $i, X37 : $i]:
% 0.46/0.62         ((v1_xboole_0 @ X36)
% 0.46/0.62          | ~ (m1_subset_1 @ X37 @ X36)
% 0.46/0.62          | (m1_subset_1 @ (k6_domain_1 @ X36 @ X37) @ (k1_zfmisc_1 @ X36)))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.46/0.62  thf('12', plain,
% 0.46/0.62      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.62        | (v1_xboole_0 @ sk_A))),
% 0.46/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.62  thf('13', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.46/0.62      inference('clc', [status(thm)], ['3', '4'])).
% 0.46/0.62  thf('14', plain,
% 0.46/0.62      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.62        | (v1_xboole_0 @ sk_A))),
% 0.46/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.62  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('16', plain,
% 0.46/0.62      ((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.62      inference('clc', [status(thm)], ['14', '15'])).
% 0.46/0.62  thf(t3_subset, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.62  thf('17', plain,
% 0.46/0.62      (![X31 : $i, X32 : $i]:
% 0.46/0.62         ((r1_tarski @ X31 @ X32) | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.62  thf('18', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.46/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.62  thf(d10_xboole_0, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.62  thf('19', plain,
% 0.46/0.62      (![X8 : $i, X10 : $i]:
% 0.46/0.62         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.46/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.62  thf('20', plain,
% 0.46/0.62      ((~ (r1_tarski @ sk_A @ (k1_tarski @ sk_B_1))
% 0.46/0.62        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.62  thf('21', plain,
% 0.46/0.62      ((((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))
% 0.46/0.62        | ~ (v1_zfmisc_1 @ sk_A)
% 0.46/0.62        | (v1_xboole_0 @ sk_A)
% 0.46/0.62        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['9', '20'])).
% 0.46/0.62  thf('22', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('23', plain,
% 0.46/0.62      ((((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))
% 0.46/0.62        | (v1_xboole_0 @ sk_A)
% 0.46/0.62        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.62  thf('24', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.62  thf('25', plain,
% 0.46/0.62      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.46/0.62        | ((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.46/0.62      inference('clc', [status(thm)], ['23', '24'])).
% 0.46/0.62  thf(commutativity_k2_tarski, axiom,
% 0.46/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.62  thf('26', plain,
% 0.46/0.62      (![X20 : $i, X21 : $i]:
% 0.46/0.62         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 0.46/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.62  thf(t12_setfam_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.62  thf('27', plain,
% 0.46/0.62      (![X29 : $i, X30 : $i]:
% 0.46/0.62         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.46/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.62  thf('28', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.62  thf('29', plain,
% 0.46/0.62      (![X29 : $i, X30 : $i]:
% 0.46/0.62         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.46/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.62  thf('30', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.62      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.62  thf(t100_xboole_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.62  thf('31', plain,
% 0.46/0.62      (![X11 : $i, X12 : $i]:
% 0.46/0.62         ((k4_xboole_0 @ X11 @ X12)
% 0.46/0.62           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.62  thf('32', plain,
% 0.46/0.62      (![X0 : $i, X1 : $i]:
% 0.46/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.62  thf('33', plain,
% 0.46/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.46/0.62          = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0))
% 0.46/0.62        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.46/0.62      inference('sup+', [status(thm)], ['25', '32'])).
% 0.46/0.62  thf(t5_boole, axiom,
% 0.46/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.62  thf('34', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.46/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.62  thf('35', plain,
% 0.46/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_tarski @ sk_B_1))
% 0.46/0.62        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.62  thf(t83_xboole_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.62  thf('36', plain,
% 0.46/0.62      (![X17 : $i, X19 : $i]:
% 0.46/0.62         ((r1_xboole_0 @ X17 @ X19) | ((k4_xboole_0 @ X17 @ X19) != (X17)))),
% 0.46/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.62  thf('37', plain,
% 0.46/0.62      ((((k1_tarski @ sk_B_1) != (k1_tarski @ sk_B_1))
% 0.46/0.62        | ((sk_A) = (k1_tarski @ sk_B_1))
% 0.46/0.62        | (r1_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.46/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.62  thf('38', plain,
% 0.46/0.62      (((r1_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.46/0.62        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.46/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.46/0.62  thf(t69_xboole_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.62       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.46/0.62  thf('39', plain,
% 0.46/0.62      (![X15 : $i, X16 : $i]:
% 0.46/0.62         (~ (r1_xboole_0 @ X15 @ X16)
% 0.46/0.62          | ~ (r1_tarski @ X15 @ X16)
% 0.46/0.62          | (v1_xboole_0 @ X15))),
% 0.46/0.62      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.46/0.62  thf('40', plain,
% 0.46/0.62      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.46/0.62        | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.46/0.62        | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.46/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.62  thf('41', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.46/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.62  thf('42', plain,
% 0.46/0.62      ((((sk_A) = (k1_tarski @ sk_B_1)) | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.46/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.62  thf('43', plain,
% 0.46/0.62      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.46/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.62  thf('44', plain,
% 0.46/0.62      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.46/0.62        | ((k1_tarski @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.62  thf(t1_boole, axiom,
% 0.46/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.62  thf('45', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.46/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.62  thf(t49_zfmisc_1, axiom,
% 0.46/0.62    (![A:$i,B:$i]:
% 0.46/0.62     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.46/0.62  thf('46', plain,
% 0.46/0.62      (![X27 : $i, X28 : $i]:
% 0.46/0.62         ((k2_xboole_0 @ (k1_tarski @ X27) @ X28) != (k1_xboole_0))),
% 0.46/0.62      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.46/0.62  thf('47', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.46/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.62  thf('48', plain, (((sk_A) = (k1_tarski @ sk_B_1))),
% 0.46/0.62      inference('simplify_reflect-', [status(thm)], ['44', '47'])).
% 0.46/0.62  thf('49', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.46/0.62      inference('demod', [status(thm)], ['6', '48'])).
% 0.46/0.62  thf(dt_l1_orders_2, axiom,
% 0.46/0.62    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.62  thf('50', plain,
% 0.46/0.62      (![X38 : $i]: ((l1_struct_0 @ X38) | ~ (l1_orders_2 @ X38))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.46/0.62  thf(t1_yellow_1, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.46/0.62       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.46/0.62  thf('51', plain,
% 0.46/0.62      (![X43 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X43)) = (X43))),
% 0.46/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.62  thf(fc12_struct_0, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( l1_struct_0 @ A ) =>
% 0.46/0.62       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.62  thf('52', plain,
% 0.46/0.62      (![X35 : $i]:
% 0.46/0.62         (~ (v1_subset_1 @ (k2_struct_0 @ X35) @ (u1_struct_0 @ X35))
% 0.46/0.62          | ~ (l1_struct_0 @ X35))),
% 0.46/0.62      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.46/0.62  thf('53', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.46/0.62          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.62  thf('54', plain,
% 0.46/0.62      (![X38 : $i]: ((l1_struct_0 @ X38) | ~ (l1_orders_2 @ X38))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.46/0.62  thf(d3_struct_0, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.62  thf('55', plain,
% 0.46/0.62      (![X34 : $i]:
% 0.46/0.62         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.46/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.62  thf('56', plain,
% 0.46/0.62      (![X43 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X43)) = (X43))),
% 0.46/0.62      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.46/0.62  thf('57', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.46/0.62          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.62      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.62  thf('58', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.62          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.46/0.62      inference('sup-', [status(thm)], ['54', '57'])).
% 0.46/0.62  thf(dt_k2_yellow_1, axiom,
% 0.46/0.62    (![A:$i]:
% 0.46/0.62     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.62       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.46/0.62  thf('59', plain, (![X42 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X42))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.62  thf('60', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.62      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.62  thf('61', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.62      inference('demod', [status(thm)], ['53', '60'])).
% 0.46/0.62  thf('62', plain,
% 0.46/0.62      (![X0 : $i]:
% 0.46/0.62         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.46/0.62      inference('sup-', [status(thm)], ['50', '61'])).
% 0.46/0.62  thf('63', plain, (![X42 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X42))),
% 0.46/0.62      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.62  thf('64', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.46/0.62      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.62  thf('65', plain, ($false), inference('sup-', [status(thm)], ['49', '64'])).
% 0.46/0.62  
% 0.46/0.62  % SZS output end Refutation
% 0.46/0.62  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
