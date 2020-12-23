%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZU51IGfLbB

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 525 expanded)
%              Number of leaves         :   36 ( 161 expanded)
%              Depth                    :   17
%              Number of atoms          : 1195 (6586 expanded)
%              Number of equality atoms :   37 (  90 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X5 @ X4 ) )
        = X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf(t11_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( X10
       != ( u1_struct_0 @ X8 ) )
      | ~ ( v1_borsuk_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v4_pre_topc @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( v1_borsuk_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( v1_borsuk_1 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( v1_borsuk_1 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      | ( v4_pre_topc @ sk_B_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_borsuk_1 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X2 @ X3 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('25',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf(cc5_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_borsuk_1 @ B @ A )
            & ( v1_tsep_1 @ B @ A )
            & ( v1_tdlat_3 @ B ) ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v1_borsuk_1 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_tdlat_3 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_borsuk_1 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_borsuk_1 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_borsuk_1 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf('37',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['20','21','22','35','36'])).

thf('38',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['8','37'])).

thf('39',plain,
    ( ( v3_tex_2 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tex_2 @ B @ A ) )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_tops_1 @ X22 @ X23 )
      | ~ ( v3_tex_2 @ X22 @ X23 )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_tdlat_3 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('47',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v3_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_tops_1 @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['38','61'])).

thf('63',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( v1_subset_1 @ sk_B_1 @ sk_B_1 )
   <= ( ( v3_tex_2 @ sk_B_1 @ sk_A )
      & ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('65',plain,(
    ! [X1: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('67',plain,(
    ! [X1: $i] :
      ~ ( v1_subset_1 @ X1 @ X1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ~ ( v3_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','68','69'])).

thf('71',plain,(
    ~ ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_tops_1 @ B @ A )
              & ( v2_tex_2 @ B @ A ) )
           => ( v3_tex_2 @ B @ A ) ) ) ) )).

thf('73',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_tex_2 @ X24 @ X25 )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ~ ( v1_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('78',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_1 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17 = X16 )
      | ( v1_subset_1 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('89',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('91',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('95',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_pre_topc @ X15 @ X14 )
       != ( u1_struct_0 @ X15 ) )
      | ( v1_tops_1 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
       != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('102',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('103',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X8 ) @ X9 )
      | ~ ( v1_borsuk_1 @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_borsuk_1 @ X0 @ sk_A )
        | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_borsuk_1 @ X0 @ sk_A )
        | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) @ sk_A )
      | ~ ( v1_borsuk_1 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('110',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('111',plain,(
    v1_borsuk_1 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['33','34'])).

thf('112',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf('113',plain,
    ( ( v4_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('115',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_tops_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','115'])).

thf('117',plain,
    ( ( v1_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ~ ( v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','68'])).

thf('119',plain,(
    v1_tops_1 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['86','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['71','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZU51IGfLbB
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:38:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 161 iterations in 0.070s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.20/0.53  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.53  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.20/0.53  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.20/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.53  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.53  thf(t49_tex_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.20/0.53         ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.53             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53              ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.53                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((~ (v3_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t52_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.53             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.53               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.53          | ~ (v4_pre_topc @ X6 @ X7)
% 0.20/0.53          | ((k2_pre_topc @ X7 @ X6) = (X6))
% 0.20/0.53          | ~ (l1_pre_topc @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.53        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t29_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.53          | ((u1_struct_0 @ (k1_pre_topc @ X5 @ X4)) = (X4))
% 0.20/0.53          | ~ (l1_pre_topc @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf(t11_tsep_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.53                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.53                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.53          | ((X10) != (u1_struct_0 @ X8))
% 0.20/0.53          | ~ (v1_borsuk_1 @ X8 @ X9)
% 0.20/0.53          | ~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.53          | (v4_pre_topc @ X10 @ X9)
% 0.20/0.53          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.53          | ~ (l1_pre_topc @ X9)
% 0.20/0.53          | ~ (v2_pre_topc @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (v2_pre_topc @ X9)
% 0.20/0.53          | ~ (l1_pre_topc @ X9)
% 0.20/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.20/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.53          | (v4_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.20/0.53          | ~ (v1_borsuk_1 @ X8 @ X9)
% 0.20/0.53          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.20/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.20/0.53          | ~ (v1_borsuk_1 @ (k1_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.20/0.53          | (v4_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.20/0.53          | ~ (v1_borsuk_1 @ (k1_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.20/0.53          | (v4_pre_topc @ sk_B_1 @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (v2_pre_topc @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.53        | ~ (v1_borsuk_1 @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '19'])).
% 0.20/0.53  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k1_pre_topc, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.53       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.20/0.53         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.20/0.53          | (m1_pre_topc @ (k1_pre_topc @ X2 @ X3) @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf(cc5_tdlat_3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.20/0.53         ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 0.20/0.53             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.53          | (v1_borsuk_1 @ X12 @ X13)
% 0.20/0.53          | ~ (l1_pre_topc @ X13)
% 0.20/0.53          | ~ (v1_tdlat_3 @ X13)
% 0.20/0.53          | ~ (v2_pre_topc @ X13)
% 0.20/0.53          | (v2_struct_0 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v1_tdlat_3 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v1_borsuk_1 @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (v1_borsuk_1 @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.20/0.53  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain, ((v1_borsuk_1 @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('37', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21', '22', '35', '36'])).
% 0.20/0.53  thf('38', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['8', '37'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (((v3_tex_2 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t47_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 0.20/0.53             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.53          | (v1_tops_1 @ X22 @ X23)
% 0.20/0.53          | ~ (v3_tex_2 @ X22 @ X23)
% 0.20/0.53          | ~ (v3_pre_topc @ X22 @ X23)
% 0.20/0.53          | ~ (l1_pre_topc @ X23)
% 0.20/0.53          | ~ (v2_pre_topc @ X23)
% 0.20/0.53          | (v2_struct_0 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t47_tex_2])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t17_tdlat_3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ( v1_tdlat_3 @ A ) <=>
% 0.20/0.53         ( ![B:$i]:
% 0.20/0.53           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (~ (v1_tdlat_3 @ X18)
% 0.20/0.53          | (v3_pre_topc @ X19 @ X18)
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.53          | ~ (l1_pre_topc @ X18)
% 0.20/0.53          | ~ (v2_pre_topc @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v3_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.53        | ~ (v1_tdlat_3 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('50', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain, ((v3_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v3_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43', '44', '51'])).
% 0.20/0.53  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A) | ~ (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (((v1_tops_1 @ sk_B_1 @ sk_A)) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d2_tops_3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v1_tops_1 @ B @ A ) <=>
% 0.20/0.53             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.53          | ~ (v1_tops_1 @ X14 @ X15)
% 0.20/0.53          | ((k2_pre_topc @ X15 @ X14) = (u1_struct_0 @ X15))
% 0.20/0.53          | ~ (l1_pre_topc @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.53  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((((k2_pre_topc @ sk_A @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '60'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((((sk_B_1) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_1 @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (((v1_subset_1 @ sk_B_1 @ sk_B_1))
% 0.20/0.53         <= (((v3_tex_2 @ sk_B_1 @ sk_A)) & 
% 0.20/0.53             ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf(fc14_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.20/0.53  thf('65', plain, (![X1 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X1) @ X1)),
% 0.20/0.53      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.20/0.53  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.53  thf('66', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.53  thf('67', plain, (![X1 : $i]: ~ (v1_subset_1 @ X1 @ X1)),
% 0.20/0.53      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.20/0.53       ~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['64', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (~ ((v3_tex_2 @ sk_B_1 @ sk_A)) | 
% 0.20/0.53       ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('70', plain, (~ ((v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['3', '68', '69'])).
% 0.20/0.53  thf('71', plain, (~ (v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['1', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t48_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.20/0.53             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.53          | (v3_tex_2 @ X24 @ X25)
% 0.20/0.53          | ~ (v2_tex_2 @ X24 @ X25)
% 0.20/0.53          | ~ (v1_tops_1 @ X24 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X25)
% 0.20/0.53          | ~ (v2_pre_topc @ X25)
% 0.20/0.53          | (v2_struct_0 @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_tex_2])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.20/0.53        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t43_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.20/0.53         ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.53          | (v2_tex_2 @ X20 @ X21)
% 0.20/0.53          | ~ (l1_pre_topc @ X21)
% 0.20/0.53          | ~ (v1_tdlat_3 @ X21)
% 0.20/0.53          | ~ (v2_pre_topc @ X21)
% 0.20/0.53          | (v2_struct_0 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t43_tex_2])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53        | ~ (v1_tdlat_3 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.53  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('81', plain, ((v1_tdlat_3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('83', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.20/0.53  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('85', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v1_tops_1 @ sk_B_1 @ sk_A)
% 0.20/0.53        | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['74', '75', '76', '85'])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d7_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (((X17) = (X16))
% 0.20/0.53          | (v1_subset_1 @ X17 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      (((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.54        | ((sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.54  thf('90', plain,
% 0.20/0.54      ((~ (v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('92', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('93', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['91', '92'])).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('95', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.54          | ((k2_pre_topc @ X15 @ X14) != (u1_struct_0 @ X15))
% 0.20/0.54          | (v1_tops_1 @ X14 @ X15)
% 0.20/0.54          | ~ (l1_pre_topc @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_tops_3])).
% 0.20/0.54  thf('96', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54           | (v1_tops_1 @ X0 @ sk_A)
% 0.20/0.54           | ((k2_pre_topc @ sk_A @ X0) != (u1_struct_0 @ sk_A))))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.54  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('98', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | (v1_tops_1 @ X0 @ sk_A)
% 0.20/0.54           | ((k2_pre_topc @ sk_A @ X0) != (sk_B_1))))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.20/0.54  thf('100', plain,
% 0.20/0.54      (((((k2_pre_topc @ sk_A @ sk_B_1) != (sk_B_1))
% 0.20/0.54         | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['93', '99'])).
% 0.20/0.54  thf('101', plain,
% 0.20/0.54      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('102', plain,
% 0.20/0.54      ((((sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('103', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (v2_pre_topc @ X9)
% 0.20/0.54          | ~ (l1_pre_topc @ X9)
% 0.20/0.54          | ~ (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.20/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.54          | (v4_pre_topc @ (u1_struct_0 @ X8) @ X9)
% 0.20/0.54          | ~ (v1_borsuk_1 @ X8 @ X9)
% 0.20/0.54          | ~ (m1_pre_topc @ X8 @ X9))),
% 0.20/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.54  thf('104', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.54           | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 0.20/0.54           | (v4_pre_topc @ (u1_struct_0 @ X0) @ sk_A)
% 0.20/0.54           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54           | ~ (v2_pre_topc @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.54  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('107', plain,
% 0.20/0.54      ((![X0 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54           | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.54           | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 0.20/0.54           | (v4_pre_topc @ (u1_struct_0 @ X0) @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.20/0.54  thf('108', plain,
% 0.20/0.54      (((~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1))
% 0.20/0.54         | (v4_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) @ sk_A)
% 0.20/0.54         | ~ (v1_borsuk_1 @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.54         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['101', '107'])).
% 0.20/0.54  thf('109', plain,
% 0.20/0.54      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_B_1)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup+', [status(thm)], ['91', '92'])).
% 0.20/0.54  thf('110', plain,
% 0.20/0.54      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('111', plain, ((v1_borsuk_1 @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.54      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('112', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('113', plain,
% 0.20/0.54      (((v4_pre_topc @ sk_B_1 @ sk_A))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.20/0.54  thf('114', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.20/0.54        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('115', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.54  thf('116', plain,
% 0.20/0.54      (((((sk_B_1) != (sk_B_1)) | (v1_tops_1 @ sk_B_1 @ sk_A)))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['100', '115'])).
% 0.20/0.54  thf('117', plain,
% 0.20/0.54      (((v1_tops_1 @ sk_B_1 @ sk_A))
% 0.20/0.54         <= (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['116'])).
% 0.20/0.54  thf('118', plain, (~ ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['3', '68'])).
% 0.20/0.54  thf('119', plain, ((v1_tops_1 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['117', '118'])).
% 0.20/0.54  thf('120', plain, (((v2_struct_0 @ sk_A) | (v3_tex_2 @ sk_B_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['86', '119'])).
% 0.20/0.54  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('122', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('clc', [status(thm)], ['120', '121'])).
% 0.20/0.54  thf('123', plain, ($false), inference('demod', [status(thm)], ['71', '122'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
