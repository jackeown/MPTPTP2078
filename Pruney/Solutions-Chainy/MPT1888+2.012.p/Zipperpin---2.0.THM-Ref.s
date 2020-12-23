%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mv4ysX9yZx

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:29 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 856 expanded)
%              Number of leaves         :   26 ( 249 expanded)
%              Depth                    :   19
%              Number of atoms          : 1832 (19397 expanded)
%              Number of equality atoms :   46 ( 461 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t56_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                | ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                  = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                  | ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                    = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_tex_2])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('3',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d4_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_tex_2 @ A @ B ) )
              <=> ( ( u1_struct_0 @ C )
                  = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( X13
       != ( k1_tex_2 @ X12 @ X11 ) )
      | ( ( u1_struct_0 @ X13 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ X11 ) )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( v1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X12 @ X11 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X12 @ X11 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X12 @ X11 ) @ X12 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X12 @ X11 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('14',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('23',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('34',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X12 @ X11 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X12 @ X11 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X12 @ X11 ) @ X12 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X12 @ X11 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('40',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('44',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('53',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['50','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['31','60'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('63',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['46','47'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('69',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('72',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t55_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
               => ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                  = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X18 ) ) )
      | ( ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) )
        = ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( v3_tdlat_3 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( sk_C @ X2 @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) ) )
        = ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ X2 @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('81',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('82',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ X0 )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('93',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['16','17'])).

thf('94',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','103'])).

thf('105',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('107',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X18 ) ) )
      | ( ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) )
        = ( k2_pre_topc @ X17 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( v3_tdlat_3 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( sk_C @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) @ X2 ) ) )
        = ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( k2_pre_topc @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) @ X2 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('111',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113','114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['104','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['91','121'])).

thf('123',plain,
    ( ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
    | ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) )
      = ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('126',plain,(
    ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('128',plain,(
    ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
 != ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['123','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('132',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['61','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mv4ysX9yZx
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:09:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 359 iterations in 0.348s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.80  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.58/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.80  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.58/0.80  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.58/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.80  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.58/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.80  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.58/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.80  thf(t56_tex_2, conjecture,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.58/0.80         ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80               ( ( r1_xboole_0 @
% 0.58/0.80                   ( k2_pre_topc @
% 0.58/0.80                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.58/0.80                   ( k2_pre_topc @
% 0.58/0.80                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.58/0.80                 ( ( k2_pre_topc @
% 0.58/0.80                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.58/0.80                   ( k2_pre_topc @
% 0.58/0.80                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i]:
% 0.58/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.80            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80          ( ![B:$i]:
% 0.58/0.80            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80              ( ![C:$i]:
% 0.58/0.80                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80                  ( ( r1_xboole_0 @
% 0.58/0.80                      ( k2_pre_topc @
% 0.58/0.80                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.58/0.80                      ( k2_pre_topc @
% 0.58/0.80                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.58/0.80                    ( ( k2_pre_topc @
% 0.58/0.80                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.58/0.80                      ( k2_pre_topc @
% 0.58/0.80                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.58/0.80  thf('0', plain,
% 0.58/0.80      (~ (r1_xboole_0 @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(dt_k1_tex_2, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.58/0.80         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.80       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.58/0.80         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.58/0.80         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (![X14 : $i, X15 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X14)
% 0.58/0.80          | (v2_struct_0 @ X14)
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.58/0.80          | (v1_pre_topc @ (k1_tex_2 @ X14 @ X15)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.80  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['3', '4'])).
% 0.58/0.80  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('7', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.58/0.80      inference('clc', [status(thm)], ['5', '6'])).
% 0.58/0.80  thf(d4_tex_2, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.58/0.80                 ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.80               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.58/0.80                 ( ( u1_struct_0 @ C ) =
% 0.58/0.80                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.58/0.80          | ((X13) != (k1_tex_2 @ X12 @ X11))
% 0.58/0.80          | ((u1_struct_0 @ X13) = (k6_domain_1 @ (u1_struct_0 @ X12) @ X11))
% 0.58/0.80          | ~ (m1_pre_topc @ X13 @ X12)
% 0.58/0.80          | ~ (v1_pre_topc @ X13)
% 0.58/0.80          | (v2_struct_0 @ X13)
% 0.58/0.80          | ~ (l1_pre_topc @ X12)
% 0.58/0.80          | (v2_struct_0 @ X12))),
% 0.58/0.80      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (![X11 : $i, X12 : $i]:
% 0.58/0.80         ((v2_struct_0 @ X12)
% 0.58/0.80          | ~ (l1_pre_topc @ X12)
% 0.58/0.80          | (v2_struct_0 @ (k1_tex_2 @ X12 @ X11))
% 0.58/0.80          | ~ (v1_pre_topc @ (k1_tex_2 @ X12 @ X11))
% 0.58/0.80          | ~ (m1_pre_topc @ (k1_tex_2 @ X12 @ X11) @ X12)
% 0.58/0.80          | ((u1_struct_0 @ (k1_tex_2 @ X12 @ X11))
% 0.58/0.80              = (k6_domain_1 @ (u1_struct_0 @ X12) @ X11))
% 0.58/0.80          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['8'])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.58/0.80        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['7', '9'])).
% 0.58/0.80  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (![X14 : $i, X15 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X14)
% 0.58/0.80          | (v2_struct_0 @ X14)
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.58/0.80          | (m1_pre_topc @ (k1_tex_2 @ X14 @ X15) @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.80  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['14', '15'])).
% 0.58/0.80  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('18', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['16', '17'])).
% 0.58/0.80  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('20', plain,
% 0.58/0.80      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.58/0.80        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80        | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['10', '11', '18', '19'])).
% 0.58/0.80  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('22', plain,
% 0.58/0.80      (![X14 : $i, X15 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X14)
% 0.58/0.80          | (v2_struct_0 @ X14)
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.58/0.80          | ~ (v2_struct_0 @ (k1_tex_2 @ X14 @ X15)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.80  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('27', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.58/0.80      inference('clc', [status(thm)], ['25', '26'])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.58/0.80      inference('clc', [status(thm)], ['20', '27'])).
% 0.58/0.80  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.80      inference('clc', [status(thm)], ['28', '29'])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      (~ (r1_xboole_0 @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.58/0.80      inference('demod', [status(thm)], ['0', '30'])).
% 0.58/0.80  thf('32', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('33', plain,
% 0.58/0.80      (![X14 : $i, X15 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X14)
% 0.58/0.80          | (v2_struct_0 @ X14)
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.58/0.80          | (v1_pre_topc @ (k1_tex_2 @ X14 @ X15)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.80  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['34', '35'])).
% 0.58/0.80  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('38', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_C_1))),
% 0.58/0.80      inference('clc', [status(thm)], ['36', '37'])).
% 0.58/0.80  thf('39', plain,
% 0.58/0.80      (![X11 : $i, X12 : $i]:
% 0.58/0.80         ((v2_struct_0 @ X12)
% 0.58/0.80          | ~ (l1_pre_topc @ X12)
% 0.58/0.80          | (v2_struct_0 @ (k1_tex_2 @ X12 @ X11))
% 0.58/0.80          | ~ (v1_pre_topc @ (k1_tex_2 @ X12 @ X11))
% 0.58/0.80          | ~ (m1_pre_topc @ (k1_tex_2 @ X12 @ X11) @ X12)
% 0.58/0.80          | ((u1_struct_0 @ (k1_tex_2 @ X12 @ X11))
% 0.58/0.80              = (k6_domain_1 @ (u1_struct_0 @ X12) @ X11))
% 0.58/0.80          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['8'])).
% 0.58/0.80  thf('40', plain,
% 0.58/0.80      ((~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.80        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.58/0.80        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_C_1) @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.80  thf('41', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('42', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('43', plain,
% 0.58/0.80      (![X14 : $i, X15 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X14)
% 0.58/0.80          | (v2_struct_0 @ X14)
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.58/0.80          | (m1_pre_topc @ (k1_tex_2 @ X14 @ X15) @ X14))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_C_1) @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.80  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('46', plain,
% 0.58/0.80      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_C_1) @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.80  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('48', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_C_1) @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['46', '47'])).
% 0.58/0.80  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('50', plain,
% 0.58/0.80      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.58/0.80        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80        | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['40', '41', '48', '49'])).
% 0.58/0.80  thf('51', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('52', plain,
% 0.58/0.80      (![X14 : $i, X15 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X14)
% 0.58/0.80          | (v2_struct_0 @ X14)
% 0.58/0.80          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.58/0.80          | ~ (v2_struct_0 @ (k1_tex_2 @ X14 @ X15)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.58/0.80  thf('53', plain,
% 0.58/0.80      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['51', '52'])).
% 0.58/0.80  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('55', plain,
% 0.58/0.80      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['53', '54'])).
% 0.58/0.80  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('57', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))),
% 0.58/0.80      inference('clc', [status(thm)], ['55', '56'])).
% 0.58/0.80  thf('58', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_A)
% 0.58/0.80        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.58/0.80      inference('clc', [status(thm)], ['50', '57'])).
% 0.58/0.80  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('60', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.58/0.80      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('61', plain,
% 0.58/0.80      (~ (r1_xboole_0 @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80          (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))))),
% 0.58/0.80      inference('demod', [status(thm)], ['31', '60'])).
% 0.58/0.80  thf(t3_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.58/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.58/0.80  thf('62', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('63', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_C_1) @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['46', '47'])).
% 0.58/0.80  thf(t1_tsep_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_pre_topc @ A ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_pre_topc @ B @ A ) =>
% 0.58/0.80           ( m1_subset_1 @
% 0.58/0.80             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.58/0.80  thf('64', plain,
% 0.58/0.80      (![X9 : $i, X10 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X9 @ X10)
% 0.58/0.80          | (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.58/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.58/0.80          | ~ (l1_pre_topc @ X10))),
% 0.58/0.80      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.58/0.80  thf('65', plain,
% 0.58/0.80      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)) @ 
% 0.58/0.80           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.80  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('67', plain,
% 0.58/0.80      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)) @ 
% 0.58/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['65', '66'])).
% 0.58/0.80  thf(dt_k2_pre_topc, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( l1_pre_topc @ A ) & 
% 0.58/0.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.80       ( m1_subset_1 @
% 0.58/0.80         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.80  thf('68', plain,
% 0.58/0.80      (![X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X7)
% 0.58/0.80          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.58/0.80          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.58/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.58/0.80  thf('69', plain,
% 0.58/0.80      (((m1_subset_1 @ 
% 0.58/0.80         (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['67', '68'])).
% 0.58/0.80  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('71', plain,
% 0.58/0.80      ((m1_subset_1 @ 
% 0.58/0.80        (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['69', '70'])).
% 0.58/0.80  thf(t4_subset, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.58/0.80       ( m1_subset_1 @ A @ C ) ))).
% 0.58/0.80  thf('72', plain,
% 0.58/0.80      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X4 @ X5)
% 0.58/0.80          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.58/0.80          | (m1_subset_1 @ X4 @ X6))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_subset])).
% 0.58/0.80  thf('73', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | ~ (r2_hidden @ X0 @ 
% 0.58/0.80               (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['71', '72'])).
% 0.58/0.80  thf('74', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80           X0)
% 0.58/0.80          | (m1_subset_1 @ 
% 0.58/0.80             (sk_C @ X0 @ 
% 0.58/0.80              (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)))) @ 
% 0.58/0.80             (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['62', '73'])).
% 0.58/0.80  thf('75', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.58/0.80      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('76', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf(t55_tex_2, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.58/0.80         ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.80               ( ( r2_hidden @
% 0.58/0.80                   B @ 
% 0.58/0.80                   ( k2_pre_topc @
% 0.58/0.80                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.58/0.80                 ( ( k2_pre_topc @
% 0.58/0.80                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.58/0.80                   ( k2_pre_topc @
% 0.58/0.80                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('77', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.58/0.80          | ~ (r2_hidden @ X16 @ 
% 0.58/0.80               (k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X18)))
% 0.58/0.80          | ((k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X16))
% 0.58/0.80              = (k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X18)))
% 0.58/0.80          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.58/0.80          | ~ (l1_pre_topc @ X17)
% 0.58/0.80          | ~ (v3_tdlat_3 @ X17)
% 0.58/0.80          | ~ (v2_pre_topc @ X17)
% 0.58/0.80          | (v2_struct_0 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.58/0.80  thf('78', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ 
% 0.58/0.80           (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)) @ X2)
% 0.58/0.80          | (v2_struct_0 @ X1)
% 0.58/0.80          | ~ (v2_pre_topc @ X1)
% 0.58/0.80          | ~ (v3_tdlat_3 @ X1)
% 0.58/0.80          | ~ (l1_pre_topc @ X1)
% 0.58/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.58/0.80          | ((k2_pre_topc @ X1 @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ X1) @ 
% 0.58/0.80               (sk_C @ X2 @ 
% 0.58/0.80                (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)))))
% 0.58/0.80              = (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)))
% 0.58/0.80          | ~ (m1_subset_1 @ 
% 0.58/0.80               (sk_C @ X2 @ 
% 0.58/0.80                (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0))) @ 
% 0.58/0.80               (u1_struct_0 @ X1)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['76', '77'])).
% 0.58/0.80  thf('79', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ 
% 0.58/0.80             (sk_C @ X0 @ 
% 0.58/0.80              (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)))) @ 
% 0.58/0.80             (u1_struct_0 @ sk_A))
% 0.58/0.80          | ((k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80               (sk_C @ X0 @ 
% 0.58/0.80                (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))
% 0.58/0.80              = (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.58/0.80          | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80          | ~ (v3_tdlat_3 @ sk_A)
% 0.58/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | (r1_xboole_0 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)) @ 
% 0.58/0.80             X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['75', '78'])).
% 0.58/0.80  thf('80', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.58/0.80      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('81', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.58/0.80      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('82', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('84', plain, ((v3_tdlat_3 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('86', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.58/0.80      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('87', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ 
% 0.58/0.80             (sk_C @ X0 @ 
% 0.58/0.80              (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)))) @ 
% 0.58/0.80             (u1_struct_0 @ sk_A))
% 0.58/0.80          | ((k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80               (sk_C @ X0 @ 
% 0.58/0.80                (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))))))
% 0.58/0.80              = (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))))
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | (r1_xboole_0 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80             X0))),
% 0.58/0.80      inference('demod', [status(thm)],
% 0.58/0.80                ['79', '80', '81', '82', '83', '84', '85', '86'])).
% 0.58/0.80  thf('88', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80           X0)
% 0.58/0.80          | (r1_xboole_0 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80             X0)
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | ((k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80               (sk_C @ X0 @ 
% 0.58/0.80                (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))))))
% 0.58/0.80              = (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['74', '87'])).
% 0.58/0.80  thf('89', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (((k2_pre_topc @ sk_A @ 
% 0.58/0.80            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80             (sk_C @ X0 @ 
% 0.58/0.80              (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))))))
% 0.58/0.80            = (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))))
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | (r1_xboole_0 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80             X0))),
% 0.58/0.80      inference('simplify', [status(thm)], ['88'])).
% 0.58/0.80  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('91', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80           X0)
% 0.58/0.80          | ((k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80               (sk_C @ X0 @ 
% 0.58/0.80                (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))))))
% 0.58/0.80              = (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)))))),
% 0.58/0.80      inference('clc', [status(thm)], ['89', '90'])).
% 0.58/0.80  thf('92', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('93', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.58/0.80      inference('clc', [status(thm)], ['16', '17'])).
% 0.58/0.80  thf('94', plain,
% 0.58/0.80      (![X9 : $i, X10 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X9 @ X10)
% 0.58/0.80          | (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.58/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.58/0.80          | ~ (l1_pre_topc @ X10))),
% 0.58/0.80      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.58/0.80  thf('95', plain,
% 0.58/0.80      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.58/0.80           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['93', '94'])).
% 0.58/0.80  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('97', plain,
% 0.58/0.80      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.58/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['95', '96'])).
% 0.58/0.80  thf('98', plain,
% 0.58/0.80      (![X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (l1_pre_topc @ X7)
% 0.58/0.80          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.58/0.80          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.58/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.58/0.80  thf('99', plain,
% 0.58/0.80      (((m1_subset_1 @ 
% 0.58/0.80         (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['97', '98'])).
% 0.58/0.80  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('101', plain,
% 0.58/0.80      ((m1_subset_1 @ 
% 0.58/0.80        (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('demod', [status(thm)], ['99', '100'])).
% 0.58/0.80  thf('102', plain,
% 0.58/0.80      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X4 @ X5)
% 0.58/0.80          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.58/0.80          | (m1_subset_1 @ X4 @ X6))),
% 0.58/0.80      inference('cnf', [status(esa)], [t4_subset])).
% 0.58/0.80  thf('103', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | ~ (r2_hidden @ X0 @ 
% 0.58/0.80               (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['101', '102'])).
% 0.58/0.80  thf('104', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.58/0.80          | (m1_subset_1 @ 
% 0.58/0.80             (sk_C @ 
% 0.58/0.80              (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80              X0) @ 
% 0.58/0.80             (u1_struct_0 @ sk_A)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['92', '103'])).
% 0.58/0.80  thf('105', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.80      inference('clc', [status(thm)], ['28', '29'])).
% 0.58/0.80  thf('106', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('107', plain,
% 0.58/0.80      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.58/0.80          | ~ (r2_hidden @ X16 @ 
% 0.58/0.80               (k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X18)))
% 0.58/0.80          | ((k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X16))
% 0.58/0.80              = (k2_pre_topc @ X17 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X18)))
% 0.58/0.80          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.58/0.80          | ~ (l1_pre_topc @ X17)
% 0.58/0.80          | ~ (v3_tdlat_3 @ X17)
% 0.58/0.80          | ~ (v2_pre_topc @ X17)
% 0.58/0.80          | (v2_struct_0 @ X17))),
% 0.58/0.80      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.58/0.80  thf('108', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X2 @ 
% 0.58/0.80           (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)))
% 0.58/0.80          | (v2_struct_0 @ X1)
% 0.58/0.80          | ~ (v2_pre_topc @ X1)
% 0.58/0.80          | ~ (v3_tdlat_3 @ X1)
% 0.58/0.80          | ~ (l1_pre_topc @ X1)
% 0.58/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.58/0.80          | ((k2_pre_topc @ X1 @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ X1) @ 
% 0.58/0.80               (sk_C @ 
% 0.58/0.80                (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)) @ 
% 0.58/0.80                X2)))
% 0.58/0.80              = (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)))
% 0.58/0.80          | ~ (m1_subset_1 @ 
% 0.58/0.80               (sk_C @ 
% 0.58/0.80                (k2_pre_topc @ X1 @ (k6_domain_1 @ (u1_struct_0 @ X1) @ X0)) @ 
% 0.58/0.80                X2) @ 
% 0.58/0.80               (u1_struct_0 @ X1)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['106', '107'])).
% 0.58/0.80  thf('109', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ 
% 0.58/0.80             (sk_C @ 
% 0.58/0.80              (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80              X0) @ 
% 0.58/0.80             (u1_struct_0 @ sk_A))
% 0.58/0.80          | ((k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80               (sk_C @ 
% 0.58/0.80                (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.58/0.80                X0)))
% 0.58/0.80              = (k2_pre_topc @ sk_A @ 
% 0.58/0.80                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.58/0.80          | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.58/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80          | ~ (v3_tdlat_3 @ sk_A)
% 0.58/0.80          | ~ (v2_pre_topc @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | (r1_xboole_0 @ X0 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['105', '108'])).
% 0.58/0.80  thf('110', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.80      inference('clc', [status(thm)], ['28', '29'])).
% 0.58/0.80  thf('111', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.80      inference('clc', [status(thm)], ['28', '29'])).
% 0.58/0.80  thf('112', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('114', plain, ((v3_tdlat_3 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('116', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.80      inference('clc', [status(thm)], ['28', '29'])).
% 0.58/0.80  thf('117', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (~ (m1_subset_1 @ 
% 0.58/0.80             (sk_C @ 
% 0.58/0.80              (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80              X0) @ 
% 0.58/0.80             (u1_struct_0 @ sk_A))
% 0.58/0.80          | ((k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80               (sk_C @ 
% 0.58/0.80                (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80                X0)))
% 0.58/0.80              = (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | (r1_xboole_0 @ X0 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))),
% 0.58/0.80      inference('demod', [status(thm)],
% 0.58/0.80                ['109', '110', '111', '112', '113', '114', '115', '116'])).
% 0.58/0.80  thf('118', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.58/0.80          | (r1_xboole_0 @ X0 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | ((k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80               (sk_C @ 
% 0.58/0.80                (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80                X0)))
% 0.58/0.80              = (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['104', '117'])).
% 0.58/0.80  thf('119', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         (((k2_pre_topc @ sk_A @ 
% 0.58/0.80            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80             (sk_C @ 
% 0.58/0.80              (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80              X0)))
% 0.58/0.80            = (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | (r1_xboole_0 @ X0 @ 
% 0.58/0.80             (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))),
% 0.58/0.80      inference('simplify', [status(thm)], ['118'])).
% 0.58/0.80  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('121', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.58/0.80          | ((k2_pre_topc @ sk_A @ 
% 0.58/0.80              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.80               (sk_C @ 
% 0.58/0.80                (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80                X0)))
% 0.58/0.80              = (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))),
% 0.58/0.80      inference('clc', [status(thm)], ['119', '120'])).
% 0.58/0.80  thf('122', plain,
% 0.58/0.80      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)))
% 0.58/0.80          = (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.58/0.80        | (r1_xboole_0 @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.58/0.80        | (r1_xboole_0 @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80           (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))),
% 0.58/0.80      inference('sup+', [status(thm)], ['91', '121'])).
% 0.58/0.80  thf('123', plain,
% 0.58/0.80      (((r1_xboole_0 @ 
% 0.58/0.80         (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80         (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.58/0.80        | ((k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1)))
% 0.58/0.80            = (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))),
% 0.58/0.80      inference('simplify', [status(thm)], ['122'])).
% 0.58/0.80  thf('124', plain,
% 0.58/0.80      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.58/0.80         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('125', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.80      inference('clc', [status(thm)], ['28', '29'])).
% 0.58/0.80  thf('126', plain,
% 0.58/0.80      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))
% 0.58/0.80         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.58/0.80      inference('demod', [status(thm)], ['124', '125'])).
% 0.58/0.80  thf('127', plain,
% 0.58/0.80      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))
% 0.58/0.80         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.58/0.80      inference('clc', [status(thm)], ['58', '59'])).
% 0.58/0.80  thf('128', plain,
% 0.58/0.80      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))
% 0.58/0.80         != (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))))),
% 0.58/0.80      inference('demod', [status(thm)], ['126', '127'])).
% 0.58/0.80  thf('129', plain,
% 0.58/0.80      ((r1_xboole_0 @ 
% 0.58/0.80        (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))) @ 
% 0.58/0.80        (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.58/0.80      inference('simplify_reflect-', [status(thm)], ['123', '128'])).
% 0.58/0.80  thf('130', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('131', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('132', plain,
% 0.58/0.80      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X2 @ X0)
% 0.58/0.80          | ~ (r2_hidden @ X2 @ X3)
% 0.58/0.80          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.80  thf('133', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X1 @ X0)
% 0.58/0.80          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.58/0.80          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.58/0.80      inference('sup-', [status(thm)], ['131', '132'])).
% 0.58/0.80  thf('134', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.58/0.80          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.58/0.80          | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['130', '133'])).
% 0.58/0.80  thf('135', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('simplify', [status(thm)], ['134'])).
% 0.58/0.80  thf('136', plain,
% 0.58/0.80      ((r1_xboole_0 @ 
% 0.58/0.80        (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))) @ 
% 0.58/0.80        (k2_pre_topc @ sk_A @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_C_1))))),
% 0.58/0.80      inference('sup-', [status(thm)], ['129', '135'])).
% 0.58/0.80  thf('137', plain, ($false), inference('demod', [status(thm)], ['61', '136'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
