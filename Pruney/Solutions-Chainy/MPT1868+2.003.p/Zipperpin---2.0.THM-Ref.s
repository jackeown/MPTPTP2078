%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EkloTWIT2R

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:39 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 338 expanded)
%              Number of leaves         :   24 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  789 (3871 expanded)
%              Number of equality atoms :   13 (  29 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

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
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('3',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(l17_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('14',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( X17
       != ( k1_tex_2 @ X16 @ X15 ) )
      | ( ( u1_struct_0 @ X17 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X16 ) @ X15 ) )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( v1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X16 @ X15 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X16 @ X15 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X16 @ X15 ) @ X16 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X16 @ X15 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X16 ) @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('28',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['25','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','35'])).

thf('37',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['33','34'])).

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

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( X28
       != ( u1_struct_0 @ X26 ) )
      | ~ ( v1_tdlat_3 @ X26 )
      | ( v2_tex_2 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('39',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X26 ) @ X27 )
      | ~ ( v1_tdlat_3 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(cc25_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v7_struct_0 @ B )
              & ( v2_pre_topc @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B )
              & ( v2_tdlat_3 @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v1_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( v7_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc25_tex_2])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('47',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','44','51'])).

thf('53',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('55',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('63',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('73',plain,(
    v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EkloTWIT2R
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 137 iterations in 0.059s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.51  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.19/0.51  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.19/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.51  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.19/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.19/0.51  thf(t36_tex_2, conjecture,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]:
% 0.19/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.51            ( l1_pre_topc @ A ) ) =>
% 0.19/0.51          ( ![B:$i]:
% 0.19/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(dt_k1_tex_2, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.19/0.51         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.19/0.51         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X20)
% 0.19/0.51          | (v2_struct_0 @ X20)
% 0.19/0.51          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.19/0.51          | (m1_pre_topc @ (k1_tex_2 @ X20 @ X21) @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.51  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('7', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.19/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf(l17_tex_2, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_pre_topc @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.51           ( m1_subset_1 @
% 0.19/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X24 : $i, X25 : $i]:
% 0.19/0.51         (~ (m1_pre_topc @ X24 @ X25)
% 0.19/0.51          | (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.19/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.19/0.51          | ~ (l1_pre_topc @ X25))),
% 0.19/0.51      inference('cnf', [status(esa)], [l17_tex_2])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.19/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.19/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.51  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X20)
% 0.19/0.51          | (v2_struct_0 @ X20)
% 0.19/0.51          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.19/0.51          | (v1_pre_topc @ (k1_tex_2 @ X20 @ X21)))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.51  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('18', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['16', '17'])).
% 0.19/0.51  thf(d4_tex_2, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.19/0.51                 ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.51               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.19/0.51                 ( ( u1_struct_0 @ C ) =
% 0.19/0.51                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.19/0.51          | ((X17) != (k1_tex_2 @ X16 @ X15))
% 0.19/0.51          | ((u1_struct_0 @ X17) = (k6_domain_1 @ (u1_struct_0 @ X16) @ X15))
% 0.19/0.51          | ~ (m1_pre_topc @ X17 @ X16)
% 0.19/0.51          | ~ (v1_pre_topc @ X17)
% 0.19/0.51          | (v2_struct_0 @ X17)
% 0.19/0.51          | ~ (l1_pre_topc @ X16)
% 0.19/0.51          | (v2_struct_0 @ X16))),
% 0.19/0.51      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (![X15 : $i, X16 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X16)
% 0.19/0.51          | ~ (l1_pre_topc @ X16)
% 0.19/0.51          | (v2_struct_0 @ (k1_tex_2 @ X16 @ X15))
% 0.19/0.51          | ~ (v1_pre_topc @ (k1_tex_2 @ X16 @ X15))
% 0.19/0.51          | ~ (m1_pre_topc @ (k1_tex_2 @ X16 @ X15) @ X16)
% 0.19/0.51          | ((u1_struct_0 @ (k1_tex_2 @ X16 @ X15))
% 0.19/0.51              = (k6_domain_1 @ (u1_struct_0 @ X16) @ X15))
% 0.19/0.51          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.19/0.51        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['18', '20'])).
% 0.19/0.51  thf('22', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('23', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.19/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.19/0.51  thf('26', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X20)
% 0.19/0.51          | (v2_struct_0 @ X20)
% 0.19/0.51          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.19/0.51          | ~ (v2_struct_0 @ (k1_tex_2 @ X20 @ X21)))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.51  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.51  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('32', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['30', '31'])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.19/0.51      inference('clc', [status(thm)], ['25', '32'])).
% 0.19/0.51  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['33', '34'])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.19/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['11', '35'])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['33', '34'])).
% 0.19/0.51  thf(t26_tex_2, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.19/0.51                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X26)
% 0.19/0.51          | ~ (m1_pre_topc @ X26 @ X27)
% 0.19/0.51          | ((X28) != (u1_struct_0 @ X26))
% 0.19/0.51          | ~ (v1_tdlat_3 @ X26)
% 0.19/0.51          | (v2_tex_2 @ X28 @ X27)
% 0.19/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.19/0.51          | ~ (l1_pre_topc @ X27)
% 0.19/0.51          | (v2_struct_0 @ X27))),
% 0.19/0.51      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (![X26 : $i, X27 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X27)
% 0.19/0.51          | ~ (l1_pre_topc @ X27)
% 0.19/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.19/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.19/0.51          | (v2_tex_2 @ (u1_struct_0 @ X26) @ X27)
% 0.19/0.51          | ~ (v1_tdlat_3 @ X26)
% 0.19/0.51          | ~ (m1_pre_topc @ X26 @ X27)
% 0.19/0.51          | (v2_struct_0 @ X26))),
% 0.19/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.19/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.51          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ X0)
% 0.19/0.51          | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ X0)
% 0.19/0.51          | ~ (l1_pre_topc @ X0)
% 0.19/0.51          | (v2_struct_0 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['37', '39'])).
% 0.19/0.51  thf('41', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.19/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf(cc25_tex_2, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.51           ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 0.19/0.51               ( v2_pre_topc @ B ) ) =>
% 0.19/0.51             ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.19/0.51               ( v2_tdlat_3 @ B ) ) ) ) ) ))).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (![X13 : $i, X14 : $i]:
% 0.19/0.51         (~ (m1_pre_topc @ X13 @ X14)
% 0.19/0.51          | (v1_tdlat_3 @ X13)
% 0.19/0.51          | ~ (v2_pre_topc @ X13)
% 0.19/0.51          | ~ (v7_struct_0 @ X13)
% 0.19/0.51          | (v2_struct_0 @ X13)
% 0.19/0.51          | ~ (l1_pre_topc @ X14)
% 0.19/0.51          | (v2_struct_0 @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc25_tex_2])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.51  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('45', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(fc2_tex_2, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.19/0.51         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.19/0.51         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (![X22 : $i, X23 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X22)
% 0.19/0.51          | (v2_struct_0 @ X22)
% 0.19/0.51          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.19/0.51          | (v7_struct_0 @ (k1_tex_2 @ X22 @ X23)))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.51  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.51  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('51', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['49', '50'])).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('demod', [status(thm)], ['43', '44', '51'])).
% 0.19/0.51  thf('53', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.19/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf(cc1_pre_topc, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.19/0.51  thf('54', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i]:
% 0.19/0.51         (~ (m1_pre_topc @ X7 @ X8)
% 0.19/0.51          | (v2_pre_topc @ X7)
% 0.19/0.51          | ~ (l1_pre_topc @ X8)
% 0.19/0.51          | ~ (v2_pre_topc @ X8))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.19/0.51  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('58', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.19/0.51  thf('59', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('demod', [status(thm)], ['52', '58'])).
% 0.19/0.51  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('61', plain,
% 0.19/0.51      (((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('clc', [status(thm)], ['59', '60'])).
% 0.19/0.51  thf('62', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['30', '31'])).
% 0.19/0.51  thf('63', plain, ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['61', '62'])).
% 0.19/0.51  thf('64', plain,
% 0.19/0.51      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['33', '34'])).
% 0.19/0.51  thf('65', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.19/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.51          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ X0)
% 0.19/0.51          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ X0)
% 0.19/0.51          | ~ (l1_pre_topc @ X0)
% 0.19/0.51          | (v2_struct_0 @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['40', '63', '64'])).
% 0.19/0.51  thf('66', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.19/0.51        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['36', '65'])).
% 0.19/0.51  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('68', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.19/0.51      inference('clc', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf('69', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.19/0.51  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('71', plain,
% 0.19/0.51      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.19/0.51      inference('clc', [status(thm)], ['69', '70'])).
% 0.19/0.51  thf('72', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['30', '31'])).
% 0.19/0.51  thf('73', plain,
% 0.19/0.51      ((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.19/0.51      inference('clc', [status(thm)], ['71', '72'])).
% 0.19/0.51  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
