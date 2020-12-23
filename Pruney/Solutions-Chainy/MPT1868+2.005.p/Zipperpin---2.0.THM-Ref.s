%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dFeNt41R5D

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:40 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 219 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  709 (2341 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(t36_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('3',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( X16
       != ( u1_struct_0 @ X14 ) )
      | ~ ( v1_tdlat_3 @ X14 )
      | ( v2_tex_2 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X14 ) @ X15 )
      | ~ ( v1_tdlat_3 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(cc3_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ~ ( v1_tdlat_3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ~ ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v1_tdlat_3 @ X6 )
      | ~ ( v7_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc3_tex_1])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('19',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('27',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','31'])).

thf('33',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('35',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','38'])).

thf('40',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('54',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

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

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( X9
       != ( k1_tex_2 @ X8 @ X7 ) )
      | ( ( u1_struct_0 @ X9 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X8 ) @ X7 ) )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( v1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X8 @ X7 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X8 @ X7 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X8 @ X7 ) @ X8 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X8 @ X7 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X8 ) @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['51','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dFeNt41R5D
% 0.14/0.38  % Computer   : n024.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 18:44:36 EST 2020
% 0.24/0.38  % CPUTime    : 
% 0.24/0.38  % Running portfolio for 600 s
% 0.24/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.24/0.38  % Number of cores: 8
% 0.24/0.38  % Python version: Python 3.6.8
% 0.24/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 32 iterations in 0.021s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.24/0.52  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.52  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.24/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.24/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.52  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.24/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.24/0.52  thf(t36_tex_2, conjecture,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i]:
% 0.24/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.52            ( l1_pre_topc @ A ) ) =>
% 0.24/0.52          ( ![B:$i]:
% 0.24/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.24/0.52  thf('0', plain,
% 0.24/0.52      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(dt_k1_tex_2, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.24/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.24/0.52         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.24/0.52         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.24/0.52  thf('2', plain,
% 0.24/0.52      (![X10 : $i, X11 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X10)
% 0.24/0.52          | (v2_struct_0 @ X10)
% 0.24/0.52          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.24/0.52          | (m1_pre_topc @ (k1_tex_2 @ X10 @ X11) @ X10))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.24/0.52  thf('3', plain,
% 0.24/0.52      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.52  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('5', plain,
% 0.24/0.52      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.24/0.52  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('7', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.24/0.52  thf(t1_tsep_1, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( l1_pre_topc @ A ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.52           ( m1_subset_1 @
% 0.24/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.24/0.52  thf('8', plain,
% 0.24/0.52      (![X4 : $i, X5 : $i]:
% 0.24/0.52         (~ (m1_pre_topc @ X4 @ X5)
% 0.24/0.52          | (m1_subset_1 @ (u1_struct_0 @ X4) @ 
% 0.24/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.24/0.52          | ~ (l1_pre_topc @ X5))),
% 0.24/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.24/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.52  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('11', plain,
% 0.24/0.52      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.24/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.52  thf(t26_tex_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.24/0.52           ( ![C:$i]:
% 0.24/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.24/0.52                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf('12', plain,
% 0.24/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.52         ((v2_struct_0 @ X14)
% 0.24/0.52          | ~ (m1_pre_topc @ X14 @ X15)
% 0.24/0.52          | ((X16) != (u1_struct_0 @ X14))
% 0.24/0.52          | ~ (v1_tdlat_3 @ X14)
% 0.24/0.52          | (v2_tex_2 @ X16 @ X15)
% 0.24/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.24/0.52          | ~ (l1_pre_topc @ X15)
% 0.24/0.52          | (v2_struct_0 @ X15))),
% 0.24/0.52      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.24/0.52  thf('13', plain,
% 0.24/0.52      (![X14 : $i, X15 : $i]:
% 0.24/0.52         ((v2_struct_0 @ X15)
% 0.24/0.52          | ~ (l1_pre_topc @ X15)
% 0.24/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.24/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.24/0.52          | (v2_tex_2 @ (u1_struct_0 @ X14) @ X15)
% 0.24/0.52          | ~ (v1_tdlat_3 @ X14)
% 0.24/0.52          | ~ (m1_pre_topc @ X14 @ X15)
% 0.24/0.52          | (v2_struct_0 @ X14))),
% 0.24/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.24/0.52  thf('14', plain,
% 0.24/0.52      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.24/0.52        | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['11', '13'])).
% 0.24/0.52  thf('15', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.24/0.52  thf(cc3_tex_1, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( l1_pre_topc @ A ) =>
% 0.24/0.52       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.52           ( ~( v1_tdlat_3 @ A ) ) ) =>
% 0.24/0.52         ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.24/0.52           ( v2_pre_topc @ A ) ) ) ))).
% 0.24/0.52  thf('16', plain,
% 0.24/0.52      (![X6 : $i]:
% 0.24/0.52         ((v2_struct_0 @ X6)
% 0.24/0.52          | ~ (v2_pre_topc @ X6)
% 0.24/0.52          | (v1_tdlat_3 @ X6)
% 0.24/0.52          | ~ (v7_struct_0 @ X6)
% 0.24/0.52          | ~ (l1_pre_topc @ X6))),
% 0.24/0.52      inference('cnf', [status(esa)], [cc3_tex_1])).
% 0.24/0.52  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('18', plain,
% 0.24/0.52      (![X10 : $i, X11 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X10)
% 0.24/0.52          | (v2_struct_0 @ X10)
% 0.24/0.52          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.24/0.52          | ~ (v2_struct_0 @ (k1_tex_2 @ X10 @ X11)))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.52  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('21', plain,
% 0.24/0.52      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.24/0.52  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('23', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      ((~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['16', '23'])).
% 0.24/0.52  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(fc2_tex_2, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.24/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.24/0.52         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.24/0.52         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.24/0.52  thf('26', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X12)
% 0.24/0.52          | (v2_struct_0 @ X12)
% 0.24/0.52          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.24/0.52          | (v7_struct_0 @ (k1_tex_2 @ X12 @ X13)))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.24/0.52  thf('27', plain,
% 0.24/0.52      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.52  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('29', plain,
% 0.24/0.52      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.24/0.52  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('31', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['29', '30'])).
% 0.24/0.52  thf('32', plain,
% 0.24/0.52      ((~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('demod', [status(thm)], ['24', '31'])).
% 0.24/0.52  thf('33', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.24/0.52  thf(cc1_pre_topc, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.24/0.52  thf('34', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]:
% 0.24/0.52         (~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.52          | (v2_pre_topc @ X0)
% 0.24/0.52          | ~ (l1_pre_topc @ X1)
% 0.24/0.52          | ~ (v2_pre_topc @ X1))),
% 0.24/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.24/0.52  thf('35', plain,
% 0.24/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.24/0.52  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('38', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.24/0.52  thf('39', plain,
% 0.24/0.52      ((~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('demod', [status(thm)], ['32', '38'])).
% 0.24/0.52  thf('40', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.24/0.52  thf(dt_m1_pre_topc, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( l1_pre_topc @ A ) =>
% 0.24/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.24/0.52  thf('41', plain,
% 0.24/0.52      (![X2 : $i, X3 : $i]:
% 0.24/0.52         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.24/0.52  thf('42', plain,
% 0.24/0.52      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.24/0.52  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('44', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.24/0.52  thf('45', plain, ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('demod', [status(thm)], ['39', '44'])).
% 0.24/0.52  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('47', plain,
% 0.24/0.52      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['14', '15', '45', '46'])).
% 0.24/0.52  thf('48', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.24/0.52  thf('49', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A)
% 0.24/0.52        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A))),
% 0.24/0.52      inference('clc', [status(thm)], ['47', '48'])).
% 0.24/0.52  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('51', plain,
% 0.24/0.52      ((v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['49', '50'])).
% 0.24/0.52  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('53', plain,
% 0.24/0.52      (![X10 : $i, X11 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X10)
% 0.24/0.52          | (v2_struct_0 @ X10)
% 0.24/0.52          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.24/0.52          | (v1_pre_topc @ (k1_tex_2 @ X10 @ X11)))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.24/0.52  thf('54', plain,
% 0.24/0.52      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.24/0.52  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('56', plain,
% 0.24/0.52      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.24/0.52  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('58', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['56', '57'])).
% 0.24/0.52  thf(d4_tex_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52           ( ![C:$i]:
% 0.24/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.24/0.52                 ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.52               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.24/0.52                 ( ( u1_struct_0 @ C ) =
% 0.24/0.52                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf('59', plain,
% 0.24/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.24/0.52          | ((X9) != (k1_tex_2 @ X8 @ X7))
% 0.24/0.52          | ((u1_struct_0 @ X9) = (k6_domain_1 @ (u1_struct_0 @ X8) @ X7))
% 0.24/0.52          | ~ (m1_pre_topc @ X9 @ X8)
% 0.24/0.52          | ~ (v1_pre_topc @ X9)
% 0.24/0.52          | (v2_struct_0 @ X9)
% 0.24/0.52          | ~ (l1_pre_topc @ X8)
% 0.24/0.52          | (v2_struct_0 @ X8))),
% 0.24/0.52      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.24/0.52  thf('60', plain,
% 0.24/0.52      (![X7 : $i, X8 : $i]:
% 0.24/0.52         ((v2_struct_0 @ X8)
% 0.24/0.52          | ~ (l1_pre_topc @ X8)
% 0.24/0.52          | (v2_struct_0 @ (k1_tex_2 @ X8 @ X7))
% 0.24/0.52          | ~ (v1_pre_topc @ (k1_tex_2 @ X8 @ X7))
% 0.24/0.52          | ~ (m1_pre_topc @ (k1_tex_2 @ X8 @ X7) @ X8)
% 0.24/0.52          | ((u1_struct_0 @ (k1_tex_2 @ X8 @ X7))
% 0.24/0.52              = (k6_domain_1 @ (u1_struct_0 @ X8) @ X7))
% 0.24/0.52          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8)))),
% 0.24/0.52      inference('simplify', [status(thm)], ['59'])).
% 0.24/0.52  thf('61', plain,
% 0.24/0.52      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.24/0.52        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['58', '60'])).
% 0.24/0.52  thf('62', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('63', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['5', '6'])).
% 0.24/0.52  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('65', plain,
% 0.24/0.52      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.24/0.52  thf('66', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['21', '22'])).
% 0.24/0.52  thf('67', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A)
% 0.24/0.52        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.24/0.52      inference('clc', [status(thm)], ['65', '66'])).
% 0.24/0.52  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('69', plain,
% 0.24/0.52      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.24/0.52         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.24/0.52      inference('clc', [status(thm)], ['67', '68'])).
% 0.24/0.52  thf('70', plain,
% 0.24/0.52      ((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.24/0.52      inference('demod', [status(thm)], ['51', '69'])).
% 0.24/0.52  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
