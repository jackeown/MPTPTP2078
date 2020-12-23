%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8WGqKJC40n

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:11 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  298 ( 949 expanded)
%              Number of leaves         :   54 ( 305 expanded)
%              Depth                    :   29
%              Number of atoms          : 2468 (10154 expanded)
%              Number of equality atoms :   80 ( 340 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('4',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( X42
        = ( u1_struct_0 @ ( sk_C_1 @ X42 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('6',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('7',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k9_setfam_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( X42
        = ( u1_struct_0 @ ( sk_C_1 @ X42 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X42 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('15',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('16',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k9_setfam_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X42 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X35: $i] :
      ( ~ ( v1_tdlat_3 @ X35 )
      | ( ( u1_pre_topc @ X35 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

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

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( X29
       != ( u1_struct_0 @ X27 ) )
      | ~ ( v1_borsuk_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v4_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X27 ) @ X28 )
      | ~ ( v1_borsuk_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('27',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X27 ) @ X28 )
      | ~ ( v1_borsuk_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_borsuk_1 @ X1 @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X1 ) @ X0 )
      | ~ ( v1_borsuk_1 @ X1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_2 @ ( u1_pre_topc @ X0 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ X0 )
      | ~ ( v1_borsuk_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X35: $i] :
      ( ~ ( v1_tdlat_3 @ X35 )
      | ( ( u1_pre_topc @ X35 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d1_tdlat_3])).

thf('36',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['31','32','33','34','40'])).

thf('42',plain,
    ( ~ ( v1_borsuk_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

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

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v1_borsuk_1 @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v1_tdlat_3 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_borsuk_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_borsuk_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_borsuk_1 @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['42','51'])).

thf('53',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['12','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('56',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('57',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k9_setfam_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('66',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( v1_tops_1 @ X50 @ X51 )
      | ~ ( v3_tex_2 @ X50 @ X51 )
      | ~ ( v3_pre_topc @ X50 @ X51 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('67',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('68',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k9_setfam_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( v1_tops_1 @ X50 @ X51 )
      | ~ ( v3_tex_2 @ X50 @ X51 )
      | ~ ( v3_pre_topc @ X50 @ X51 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('73',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_tdlat_3 @ X44 )
      | ( v3_pre_topc @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('74',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('75',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_tdlat_3 @ X44 )
      | ( v3_pre_topc @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k9_setfam_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v3_pre_topc @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('86',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v1_tops_1 @ X36 @ X37 )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('87',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('88',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k9_setfam_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v1_tops_1 @ X36 @ X37 )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,
    ( ( ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['62','92'])).

thf('94',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('95',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('96',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v3_tex_2 @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('97',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('98',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_xboole_0 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k9_setfam_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v3_tex_2 @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','104'])).

thf('106',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['93','105'])).

thf('107',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('108',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( ( v3_tex_2 @ sk_B_2 @ sk_A )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('109',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_subset_1 @ X39 @ X38 )
      | ( X39 != X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('110',plain,(
    ! [X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( v1_subset_1 @ X38 @ X38 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('112',plain,(
    ! [X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k9_setfam_1 @ X38 ) )
      | ~ ( v1_subset_1 @ X38 @ X38 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('113',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('114',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('115',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('116',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k9_setfam_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X38: $i] :
      ~ ( v1_subset_1 @ X38 @ X38 ) ),
    inference(demod,[status(thm)],['112','116'])).

thf('118',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','117'])).

thf('119',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('120',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('121',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 = X38 )
      | ( v1_subset_1 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('122',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('123',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 = X38 )
      | ( v1_subset_1 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k9_setfam_1 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['63'])).

thf('126',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k9_setfam_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('128',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k9_setfam_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( X42
        = ( u1_struct_0 @ ( sk_C_1 @ X42 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k9_setfam_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('131',plain,(
    ! [X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k9_setfam_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X42 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('134',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( v1_borsuk_1 @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v1_tdlat_3 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_borsuk_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_borsuk_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('138',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('139',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('140',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X27 ) @ X28 )
      | ~ ( v1_borsuk_1 @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_borsuk_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( v1_borsuk_1 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( ( v4_pre_topc @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['126','151'])).

thf('153',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( v4_pre_topc @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v4_pre_topc @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('161',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
        = sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('163',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ X36 )
       != ( u1_struct_0 @ X37 ) )
      | ( v1_tops_1 @ X36 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('164',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('165',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k9_setfam_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ X36 )
       != ( u1_struct_0 @ X37 ) )
      | ( v1_tops_1 @ X36 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( sk_B_2
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_tops_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['161','168'])).

thf('170',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('171',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_tops_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( ( v1_tops_1 @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('174',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( v3_tex_2 @ X52 @ X53 )
      | ~ ( v2_tex_2 @ X52 @ X53 )
      | ~ ( v1_tops_1 @ X52 @ X53 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('175',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('176',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k9_setfam_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( v3_tex_2 @ X52 @ X53 )
      | ~ ( v2_tex_2 @ X52 @ X53 )
      | ~ ( v1_tops_1 @ X52 @ X53 )
      | ~ ( l1_pre_topc @ X53 )
      | ~ ( v2_pre_topc @ X53 )
      | ( v2_struct_0 @ X53 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('181',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( v2_tex_2 @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v1_tdlat_3 @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('182',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('183',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k9_setfam_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( v2_tex_2 @ X46 @ X47 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v1_tdlat_3 @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['180','183'])).

thf('185',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['177','178','179','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v3_tex_2 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['172','193'])).

thf('195',plain,
    ( ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('196',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('197',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('198',plain,(
    ! [X9: $i] :
      ( ( k1_subset_1 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('199',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('200',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 = X38 )
      | ( v1_subset_1 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k9_setfam_1 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('204',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( v1_subset_1 @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('205',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('206',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k9_setfam_1 @ X19 ) )
      | ~ ( v1_subset_1 @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['203','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['202','207'])).

thf('209',plain,
    ( ( k1_xboole_0 = sk_B_2 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','208'])).

thf('210',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('211',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('212',plain,(
    ! [X20: $i] :
      ( ( k9_setfam_1 @ X20 )
      = ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('213',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X24 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,
    ( ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k9_setfam_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['210','213'])).

thf('215',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k9_setfam_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k9_setfam_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 = X38 )
      | ( v1_subset_1 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k9_setfam_1 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('221',plain,
    ( ( ( v1_subset_1 @ ( sk_B @ sk_A ) @ sk_B_2 )
      | ( ( sk_B @ sk_A )
        = sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k9_setfam_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['217','218'])).

thf('223',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k9_setfam_1 @ X19 ) )
      | ~ ( v1_subset_1 @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('224',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_subset_1 @ ( sk_B @ sk_A ) @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,
    ( ( ( ( sk_B @ sk_A )
        = sk_B_2 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['221','224'])).

thf('226',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = sk_B_2 ) )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','225'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('227',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('228',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('229',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['227','230'])).

thf('232',plain,
    ( ( k1_xboole_0 = sk_B_2 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','208'])).

thf('233',plain,
    ( ( ( sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['226','231','232'])).

thf('234',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('235',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['227','230'])).

thf('237',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['235','236','237','238'])).

thf('240',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','118','119','241'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8WGqKJC40n
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.58/1.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.58/1.77  % Solved by: fo/fo7.sh
% 1.58/1.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.58/1.77  % done 1676 iterations in 1.312s
% 1.58/1.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.58/1.77  % SZS output start Refutation
% 1.58/1.77  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.58/1.77  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 1.58/1.77  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.58/1.77  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.58/1.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.58/1.77  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.58/1.77  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.58/1.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.58/1.77  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.58/1.77  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.58/1.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.58/1.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.58/1.77  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.58/1.77  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.58/1.77  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.58/1.77  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.58/1.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.58/1.77  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.58/1.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.58/1.77  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 1.58/1.77  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.58/1.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.58/1.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.58/1.77  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 1.58/1.77  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.58/1.77  thf(sk_A_type, type, sk_A: $i).
% 1.58/1.77  thf(sk_B_type, type, sk_B: $i > $i).
% 1.58/1.77  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 1.58/1.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.58/1.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.58/1.77  thf(t49_tex_2, conjecture,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 1.58/1.77         ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.58/1.77           ( ( v3_tex_2 @ B @ A ) <=>
% 1.58/1.77             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.58/1.77  thf(zf_stmt_0, negated_conjecture,
% 1.58/1.77    (~( ![A:$i]:
% 1.58/1.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.58/1.77            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.58/1.77          ( ![B:$i]:
% 1.58/1.77            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.58/1.77              ( ( v3_tex_2 @ B @ A ) <=>
% 1.58/1.77                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 1.58/1.77    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 1.58/1.77  thf('0', plain,
% 1.58/1.77      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 1.58/1.77        | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('1', plain,
% 1.58/1.77      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 1.58/1.77       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('split', [status(esa)], ['0'])).
% 1.58/1.77  thf('2', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf(redefinition_k9_setfam_1, axiom,
% 1.58/1.77    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 1.58/1.77  thf('3', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('4', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf(t10_tsep_1, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.58/1.77             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.58/1.77           ( ?[C:$i]:
% 1.58/1.77             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 1.58/1.77               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 1.58/1.77  thf('5', plain,
% 1.58/1.77      (![X42 : $i, X43 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ X42)
% 1.58/1.77          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.58/1.77          | ((X42) = (u1_struct_0 @ (sk_C_1 @ X42 @ X43)))
% 1.58/1.77          | ~ (l1_pre_topc @ X43)
% 1.58/1.77          | (v2_struct_0 @ X43))),
% 1.58/1.77      inference('cnf', [status(esa)], [t10_tsep_1])).
% 1.58/1.77  thf('6', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('7', plain,
% 1.58/1.77      (![X42 : $i, X43 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ X42)
% 1.58/1.77          | ~ (m1_subset_1 @ X42 @ (k9_setfam_1 @ (u1_struct_0 @ X43)))
% 1.58/1.77          | ((X42) = (u1_struct_0 @ (sk_C_1 @ X42 @ X43)))
% 1.58/1.77          | ~ (l1_pre_topc @ X43)
% 1.58/1.77          | (v2_struct_0 @ X43))),
% 1.58/1.77      inference('demod', [status(thm)], ['5', '6'])).
% 1.58/1.77  thf('8', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('sup-', [status(thm)], ['4', '7'])).
% 1.58/1.77  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('10', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('demod', [status(thm)], ['8', '9'])).
% 1.58/1.77  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('12', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))))),
% 1.58/1.77      inference('clc', [status(thm)], ['10', '11'])).
% 1.58/1.77  thf('13', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf('14', plain,
% 1.58/1.77      (![X42 : $i, X43 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ X42)
% 1.58/1.77          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.58/1.77          | (m1_pre_topc @ (sk_C_1 @ X42 @ X43) @ X43)
% 1.58/1.77          | ~ (l1_pre_topc @ X43)
% 1.58/1.77          | (v2_struct_0 @ X43))),
% 1.58/1.77      inference('cnf', [status(esa)], [t10_tsep_1])).
% 1.58/1.77  thf('15', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('16', plain,
% 1.58/1.77      (![X42 : $i, X43 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ X42)
% 1.58/1.77          | ~ (m1_subset_1 @ X42 @ (k9_setfam_1 @ (u1_struct_0 @ X43)))
% 1.58/1.77          | (m1_pre_topc @ (sk_C_1 @ X42 @ X43) @ X43)
% 1.58/1.77          | ~ (l1_pre_topc @ X43)
% 1.58/1.77          | (v2_struct_0 @ X43))),
% 1.58/1.77      inference('demod', [status(thm)], ['14', '15'])).
% 1.58/1.77  thf('17', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('sup-', [status(thm)], ['13', '16'])).
% 1.58/1.77  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('19', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('demod', [status(thm)], ['17', '18'])).
% 1.58/1.77  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('21', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))),
% 1.58/1.77      inference('clc', [status(thm)], ['19', '20'])).
% 1.58/1.77  thf('22', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))))),
% 1.58/1.77      inference('clc', [status(thm)], ['10', '11'])).
% 1.58/1.77  thf(d1_tdlat_3, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( l1_pre_topc @ A ) =>
% 1.58/1.77       ( ( v1_tdlat_3 @ A ) <=>
% 1.58/1.77         ( ( u1_pre_topc @ A ) = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.58/1.77  thf('23', plain,
% 1.58/1.77      (![X35 : $i]:
% 1.58/1.77         (~ (v1_tdlat_3 @ X35)
% 1.58/1.77          | ((u1_pre_topc @ X35) = (k9_setfam_1 @ (u1_struct_0 @ X35)))
% 1.58/1.77          | ~ (l1_pre_topc @ X35))),
% 1.58/1.77      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 1.58/1.77  thf(t11_tsep_1, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_pre_topc @ B @ A ) =>
% 1.58/1.77           ( ![C:$i]:
% 1.58/1.77             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.58/1.77               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.58/1.77                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 1.58/1.77                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 1.58/1.77  thf('24', plain,
% 1.58/1.77      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.58/1.77         (~ (m1_pre_topc @ X27 @ X28)
% 1.58/1.77          | ((X29) != (u1_struct_0 @ X27))
% 1.58/1.77          | ~ (v1_borsuk_1 @ X27 @ X28)
% 1.58/1.77          | ~ (m1_pre_topc @ X27 @ X28)
% 1.58/1.77          | (v4_pre_topc @ X29 @ X28)
% 1.58/1.77          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.58/1.77          | ~ (l1_pre_topc @ X28)
% 1.58/1.77          | ~ (v2_pre_topc @ X28))),
% 1.58/1.77      inference('cnf', [status(esa)], [t11_tsep_1])).
% 1.58/1.77  thf('25', plain,
% 1.58/1.77      (![X27 : $i, X28 : $i]:
% 1.58/1.77         (~ (v2_pre_topc @ X28)
% 1.58/1.77          | ~ (l1_pre_topc @ X28)
% 1.58/1.77          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 1.58/1.77               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.58/1.77          | (v4_pre_topc @ (u1_struct_0 @ X27) @ X28)
% 1.58/1.77          | ~ (v1_borsuk_1 @ X27 @ X28)
% 1.58/1.77          | ~ (m1_pre_topc @ X27 @ X28))),
% 1.58/1.77      inference('simplify', [status(thm)], ['24'])).
% 1.58/1.77  thf('26', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('27', plain,
% 1.58/1.77      (![X27 : $i, X28 : $i]:
% 1.58/1.77         (~ (v2_pre_topc @ X28)
% 1.58/1.77          | ~ (l1_pre_topc @ X28)
% 1.58/1.77          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 1.58/1.77               (k9_setfam_1 @ (u1_struct_0 @ X28)))
% 1.58/1.77          | (v4_pre_topc @ (u1_struct_0 @ X27) @ X28)
% 1.58/1.77          | ~ (v1_borsuk_1 @ X27 @ X28)
% 1.58/1.77          | ~ (m1_pre_topc @ X27 @ X28))),
% 1.58/1.77      inference('demod', [status(thm)], ['25', '26'])).
% 1.58/1.77  thf('28', plain,
% 1.58/1.77      (![X0 : $i, X1 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | ~ (m1_pre_topc @ X1 @ X0)
% 1.58/1.77          | ~ (v1_borsuk_1 @ X1 @ X0)
% 1.58/1.77          | (v4_pre_topc @ (u1_struct_0 @ X1) @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0))),
% 1.58/1.77      inference('sup-', [status(thm)], ['23', '27'])).
% 1.58/1.77  thf('29', plain,
% 1.58/1.77      (![X0 : $i, X1 : $i]:
% 1.58/1.77         (~ (v2_pre_topc @ X0)
% 1.58/1.77          | (v4_pre_topc @ (u1_struct_0 @ X1) @ X0)
% 1.58/1.77          | ~ (v1_borsuk_1 @ X1 @ X0)
% 1.58/1.77          | ~ (m1_pre_topc @ X1 @ X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | ~ (m1_subset_1 @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X0)))),
% 1.58/1.77      inference('simplify', [status(thm)], ['28'])).
% 1.58/1.77  thf('30', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ sk_B_2 @ (u1_pre_topc @ X0))
% 1.58/1.77          | (v1_xboole_0 @ sk_B_2)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | ~ (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ X0)
% 1.58/1.77          | ~ (v1_borsuk_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ X0)
% 1.58/1.77          | (v4_pre_topc @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0))),
% 1.58/1.77      inference('sup-', [status(thm)], ['22', '29'])).
% 1.58/1.77  thf('31', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | ~ (v2_pre_topc @ sk_A)
% 1.58/1.77        | (v4_pre_topc @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A)
% 1.58/1.77        | ~ (v1_borsuk_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 1.58/1.77        | ~ (v1_tdlat_3 @ sk_A)
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | ~ (m1_subset_1 @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['21', '30'])).
% 1.58/1.77  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('33', plain, ((v1_tdlat_3 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('35', plain,
% 1.58/1.77      (![X35 : $i]:
% 1.58/1.77         (~ (v1_tdlat_3 @ X35)
% 1.58/1.77          | ((u1_pre_topc @ X35) = (k9_setfam_1 @ (u1_struct_0 @ X35)))
% 1.58/1.77          | ~ (l1_pre_topc @ X35))),
% 1.58/1.77      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 1.58/1.77  thf('36', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf('37', plain,
% 1.58/1.77      (((m1_subset_1 @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | ~ (v1_tdlat_3 @ sk_A))),
% 1.58/1.77      inference('sup+', [status(thm)], ['35', '36'])).
% 1.58/1.77  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('39', plain, ((v1_tdlat_3 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('40', plain, ((m1_subset_1 @ sk_B_2 @ (u1_pre_topc @ sk_A))),
% 1.58/1.77      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.58/1.77  thf('41', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | (v4_pre_topc @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A)
% 1.58/1.77        | ~ (v1_borsuk_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('demod', [status(thm)], ['31', '32', '33', '34', '40'])).
% 1.58/1.77  thf('42', plain,
% 1.58/1.77      ((~ (v1_borsuk_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 1.58/1.77        | (v4_pre_topc @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A)
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('simplify', [status(thm)], ['41'])).
% 1.58/1.77  thf('43', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))),
% 1.58/1.77      inference('clc', [status(thm)], ['19', '20'])).
% 1.58/1.77  thf(cc5_tdlat_3, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 1.58/1.77         ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_pre_topc @ B @ A ) =>
% 1.58/1.77           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 1.58/1.77             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 1.58/1.77  thf('44', plain,
% 1.58/1.77      (![X33 : $i, X34 : $i]:
% 1.58/1.77         (~ (m1_pre_topc @ X33 @ X34)
% 1.58/1.77          | (v1_borsuk_1 @ X33 @ X34)
% 1.58/1.77          | ~ (l1_pre_topc @ X34)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X34)
% 1.58/1.77          | ~ (v2_pre_topc @ X34)
% 1.58/1.77          | (v2_struct_0 @ X34))),
% 1.58/1.77      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 1.58/1.77  thf('45', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | (v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (v2_pre_topc @ sk_A)
% 1.58/1.77        | ~ (v1_tdlat_3 @ sk_A)
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | (v1_borsuk_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))),
% 1.58/1.77      inference('sup-', [status(thm)], ['43', '44'])).
% 1.58/1.77  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('47', plain, ((v1_tdlat_3 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('49', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | (v2_struct_0 @ sk_A)
% 1.58/1.77        | (v1_borsuk_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))),
% 1.58/1.77      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 1.58/1.77  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('51', plain,
% 1.58/1.77      (((v1_borsuk_1 @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('clc', [status(thm)], ['49', '50'])).
% 1.58/1.77  thf('52', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | (v4_pre_topc @ (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)) @ sk_A))),
% 1.58/1.77      inference('clc', [status(thm)], ['42', '51'])).
% 1.58/1.77  thf('53', plain,
% 1.58/1.77      (((v4_pre_topc @ sk_B_2 @ sk_A)
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2)
% 1.58/1.77        | (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('sup+', [status(thm)], ['12', '52'])).
% 1.58/1.77  thf('54', plain, (((v1_xboole_0 @ sk_B_2) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('simplify', [status(thm)], ['53'])).
% 1.58/1.77  thf('55', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf(t52_pre_topc, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( l1_pre_topc @ A ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.58/1.77           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.58/1.77             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.58/1.77               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.58/1.77  thf('56', plain,
% 1.58/1.77      (![X25 : $i, X26 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.58/1.77          | ~ (v4_pre_topc @ X25 @ X26)
% 1.58/1.77          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 1.58/1.77          | ~ (l1_pre_topc @ X26))),
% 1.58/1.77      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.58/1.77  thf('57', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('58', plain,
% 1.58/1.77      (![X25 : $i, X26 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X25 @ (k9_setfam_1 @ (u1_struct_0 @ X26)))
% 1.58/1.77          | ~ (v4_pre_topc @ X25 @ X26)
% 1.58/1.77          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 1.58/1.77          | ~ (l1_pre_topc @ X26))),
% 1.58/1.77      inference('demod', [status(thm)], ['56', '57'])).
% 1.58/1.77  thf('59', plain,
% 1.58/1.77      ((~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 1.58/1.77        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('sup-', [status(thm)], ['55', '58'])).
% 1.58/1.77  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('61', plain,
% 1.58/1.77      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 1.58/1.77        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('demod', [status(thm)], ['59', '60'])).
% 1.58/1.77  thf('62', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2) | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['54', '61'])).
% 1.58/1.77  thf('63', plain,
% 1.58/1.77      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 1.58/1.77        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('64', plain,
% 1.58/1.77      (((v3_tex_2 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('split', [status(esa)], ['63'])).
% 1.58/1.77  thf('65', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf(t47_tex_2, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.58/1.77           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 1.58/1.77             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 1.58/1.77  thf('66', plain,
% 1.58/1.77      (![X50 : $i, X51 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 1.58/1.77          | (v1_tops_1 @ X50 @ X51)
% 1.58/1.77          | ~ (v3_tex_2 @ X50 @ X51)
% 1.58/1.77          | ~ (v3_pre_topc @ X50 @ X51)
% 1.58/1.77          | ~ (l1_pre_topc @ X51)
% 1.58/1.77          | ~ (v2_pre_topc @ X51)
% 1.58/1.77          | (v2_struct_0 @ X51))),
% 1.58/1.77      inference('cnf', [status(esa)], [t47_tex_2])).
% 1.58/1.77  thf('67', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('68', plain,
% 1.58/1.77      (![X50 : $i, X51 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X50 @ (k9_setfam_1 @ (u1_struct_0 @ X51)))
% 1.58/1.77          | (v1_tops_1 @ X50 @ X51)
% 1.58/1.77          | ~ (v3_tex_2 @ X50 @ X51)
% 1.58/1.77          | ~ (v3_pre_topc @ X50 @ X51)
% 1.58/1.77          | ~ (l1_pre_topc @ X51)
% 1.58/1.77          | ~ (v2_pre_topc @ X51)
% 1.58/1.77          | (v2_struct_0 @ X51))),
% 1.58/1.77      inference('demod', [status(thm)], ['66', '67'])).
% 1.58/1.77  thf('69', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (v2_pre_topc @ sk_A)
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 1.58/1.77        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 1.58/1.77        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('sup-', [status(thm)], ['65', '68'])).
% 1.58/1.77  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('72', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf(t17_tdlat_3, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ( v1_tdlat_3 @ A ) <=>
% 1.58/1.77         ( ![B:$i]:
% 1.58/1.77           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.58/1.77             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 1.58/1.77  thf('73', plain,
% 1.58/1.77      (![X44 : $i, X45 : $i]:
% 1.58/1.77         (~ (v1_tdlat_3 @ X44)
% 1.58/1.77          | (v3_pre_topc @ X45 @ X44)
% 1.58/1.77          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.58/1.77          | ~ (l1_pre_topc @ X44)
% 1.58/1.77          | ~ (v2_pre_topc @ X44))),
% 1.58/1.77      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 1.58/1.77  thf('74', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('75', plain,
% 1.58/1.77      (![X44 : $i, X45 : $i]:
% 1.58/1.77         (~ (v1_tdlat_3 @ X44)
% 1.58/1.77          | (v3_pre_topc @ X45 @ X44)
% 1.58/1.77          | ~ (m1_subset_1 @ X45 @ (k9_setfam_1 @ (u1_struct_0 @ X44)))
% 1.58/1.77          | ~ (l1_pre_topc @ X44)
% 1.58/1.77          | ~ (v2_pre_topc @ X44))),
% 1.58/1.77      inference('demod', [status(thm)], ['73', '74'])).
% 1.58/1.77  thf('76', plain,
% 1.58/1.77      ((~ (v2_pre_topc @ sk_A)
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 1.58/1.77        | ~ (v1_tdlat_3 @ sk_A))),
% 1.58/1.77      inference('sup-', [status(thm)], ['72', '75'])).
% 1.58/1.77  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('79', plain, ((v1_tdlat_3 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('80', plain, ((v3_pre_topc @ sk_B_2 @ sk_A)),
% 1.58/1.77      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 1.58/1.77  thf('81', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 1.58/1.77        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('demod', [status(thm)], ['69', '70', '71', '80'])).
% 1.58/1.77  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('83', plain,
% 1.58/1.77      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('clc', [status(thm)], ['81', '82'])).
% 1.58/1.77  thf('84', plain,
% 1.58/1.77      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['64', '83'])).
% 1.58/1.77  thf('85', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf(d2_tops_3, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( l1_pre_topc @ A ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.58/1.77           ( ( v1_tops_1 @ B @ A ) <=>
% 1.58/1.77             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.58/1.77  thf('86', plain,
% 1.58/1.77      (![X36 : $i, X37 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.58/1.77          | ~ (v1_tops_1 @ X36 @ X37)
% 1.58/1.77          | ((k2_pre_topc @ X37 @ X36) = (u1_struct_0 @ X37))
% 1.58/1.77          | ~ (l1_pre_topc @ X37))),
% 1.58/1.77      inference('cnf', [status(esa)], [d2_tops_3])).
% 1.58/1.77  thf('87', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('88', plain,
% 1.58/1.77      (![X36 : $i, X37 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X36 @ (k9_setfam_1 @ (u1_struct_0 @ X37)))
% 1.58/1.77          | ~ (v1_tops_1 @ X36 @ X37)
% 1.58/1.77          | ((k2_pre_topc @ X37 @ X36) = (u1_struct_0 @ X37))
% 1.58/1.77          | ~ (l1_pre_topc @ X37))),
% 1.58/1.77      inference('demod', [status(thm)], ['86', '87'])).
% 1.58/1.77  thf('89', plain,
% 1.58/1.77      ((~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 1.58/1.77        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('sup-', [status(thm)], ['85', '88'])).
% 1.58/1.77  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('91', plain,
% 1.58/1.77      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 1.58/1.77        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('demod', [status(thm)], ['89', '90'])).
% 1.58/1.77  thf('92', plain,
% 1.58/1.77      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 1.58/1.77         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['84', '91'])).
% 1.58/1.77  thf('93', plain,
% 1.58/1.77      (((((sk_B_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_2)))
% 1.58/1.77         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('sup+', [status(thm)], ['62', '92'])).
% 1.58/1.77  thf('94', plain,
% 1.58/1.77      (((v3_tex_2 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('split', [status(esa)], ['63'])).
% 1.58/1.77  thf('95', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf(t46_tex_2, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( ( v1_xboole_0 @ B ) & 
% 1.58/1.77             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.58/1.77           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.58/1.77  thf('96', plain,
% 1.58/1.77      (![X48 : $i, X49 : $i]:
% 1.58/1.77         (~ (v1_xboole_0 @ X48)
% 1.58/1.77          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 1.58/1.77          | ~ (v3_tex_2 @ X48 @ X49)
% 1.58/1.77          | ~ (l1_pre_topc @ X49)
% 1.58/1.77          | ~ (v2_pre_topc @ X49)
% 1.58/1.77          | (v2_struct_0 @ X49))),
% 1.58/1.77      inference('cnf', [status(esa)], [t46_tex_2])).
% 1.58/1.77  thf('97', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('98', plain,
% 1.58/1.77      (![X48 : $i, X49 : $i]:
% 1.58/1.77         (~ (v1_xboole_0 @ X48)
% 1.58/1.77          | ~ (m1_subset_1 @ X48 @ (k9_setfam_1 @ (u1_struct_0 @ X49)))
% 1.58/1.77          | ~ (v3_tex_2 @ X48 @ X49)
% 1.58/1.77          | ~ (l1_pre_topc @ X49)
% 1.58/1.77          | ~ (v2_pre_topc @ X49)
% 1.58/1.77          | (v2_struct_0 @ X49))),
% 1.58/1.77      inference('demod', [status(thm)], ['96', '97'])).
% 1.58/1.77  thf('99', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (v2_pre_topc @ sk_A)
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 1.58/1.77        | ~ (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('sup-', [status(thm)], ['95', '98'])).
% 1.58/1.77  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('102', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 1.58/1.77        | ~ (v1_xboole_0 @ sk_B_2))),
% 1.58/1.77      inference('demod', [status(thm)], ['99', '100', '101'])).
% 1.58/1.77  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('104', plain,
% 1.58/1.77      ((~ (v1_xboole_0 @ sk_B_2) | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('clc', [status(thm)], ['102', '103'])).
% 1.58/1.77  thf('105', plain,
% 1.58/1.77      ((~ (v1_xboole_0 @ sk_B_2)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['94', '104'])).
% 1.58/1.77  thf('106', plain,
% 1.58/1.77      ((((sk_B_2) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('clc', [status(thm)], ['93', '105'])).
% 1.58/1.77  thf('107', plain,
% 1.58/1.77      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 1.58/1.77         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('split', [status(esa)], ['0'])).
% 1.58/1.77  thf('108', plain,
% 1.58/1.77      (((v1_subset_1 @ sk_B_2 @ sk_B_2))
% 1.58/1.77         <= (((v3_tex_2 @ sk_B_2 @ sk_A)) & 
% 1.58/1.77             ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup+', [status(thm)], ['106', '107'])).
% 1.58/1.77  thf(d7_subset_1, axiom,
% 1.58/1.77    (![A:$i,B:$i]:
% 1.58/1.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.58/1.77       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 1.58/1.77  thf('109', plain,
% 1.58/1.77      (![X38 : $i, X39 : $i]:
% 1.58/1.77         (~ (v1_subset_1 @ X39 @ X38)
% 1.58/1.77          | ((X39) != (X38))
% 1.58/1.77          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 1.58/1.77      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.58/1.77  thf('110', plain,
% 1.58/1.77      (![X38 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X38))
% 1.58/1.77          | ~ (v1_subset_1 @ X38 @ X38))),
% 1.58/1.77      inference('simplify', [status(thm)], ['109'])).
% 1.58/1.77  thf('111', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('112', plain,
% 1.58/1.77      (![X38 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X38 @ (k9_setfam_1 @ X38))
% 1.58/1.77          | ~ (v1_subset_1 @ X38 @ X38))),
% 1.58/1.77      inference('demod', [status(thm)], ['110', '111'])).
% 1.58/1.77  thf(dt_k2_subset_1, axiom,
% 1.58/1.77    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.58/1.77  thf('113', plain,
% 1.58/1.77      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 1.58/1.77      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.58/1.77  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.58/1.77  thf('114', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 1.58/1.77      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.58/1.77  thf('115', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('116', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k9_setfam_1 @ X12))),
% 1.58/1.77      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.58/1.77  thf('117', plain, (![X38 : $i]: ~ (v1_subset_1 @ X38 @ X38)),
% 1.58/1.77      inference('demod', [status(thm)], ['112', '116'])).
% 1.58/1.77  thf('118', plain,
% 1.58/1.77      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 1.58/1.77       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('sup-', [status(thm)], ['108', '117'])).
% 1.58/1.77  thf('119', plain,
% 1.58/1.77      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 1.58/1.77       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('split', [status(esa)], ['63'])).
% 1.58/1.77  thf('120', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf('121', plain,
% 1.58/1.77      (![X38 : $i, X39 : $i]:
% 1.58/1.77         (((X39) = (X38))
% 1.58/1.77          | (v1_subset_1 @ X39 @ X38)
% 1.58/1.77          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 1.58/1.77      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.58/1.77  thf('122', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('123', plain,
% 1.58/1.77      (![X38 : $i, X39 : $i]:
% 1.58/1.77         (((X39) = (X38))
% 1.58/1.77          | (v1_subset_1 @ X39 @ X38)
% 1.58/1.77          | ~ (m1_subset_1 @ X39 @ (k9_setfam_1 @ X38)))),
% 1.58/1.77      inference('demod', [status(thm)], ['121', '122'])).
% 1.58/1.77  thf('124', plain,
% 1.58/1.77      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 1.58/1.77        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['120', '123'])).
% 1.58/1.77  thf('125', plain,
% 1.58/1.77      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('split', [status(esa)], ['63'])).
% 1.58/1.77  thf('126', plain,
% 1.58/1.77      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['124', '125'])).
% 1.58/1.77  thf('127', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k9_setfam_1 @ X12))),
% 1.58/1.77      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.58/1.77  thf('128', plain,
% 1.58/1.77      (![X42 : $i, X43 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ X42)
% 1.58/1.77          | ~ (m1_subset_1 @ X42 @ (k9_setfam_1 @ (u1_struct_0 @ X43)))
% 1.58/1.77          | ((X42) = (u1_struct_0 @ (sk_C_1 @ X42 @ X43)))
% 1.58/1.77          | ~ (l1_pre_topc @ X43)
% 1.58/1.77          | (v2_struct_0 @ X43))),
% 1.58/1.77      inference('demod', [status(thm)], ['5', '6'])).
% 1.58/1.77  thf('129', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | ((u1_struct_0 @ X0)
% 1.58/1.77              = (u1_struct_0 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)))
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['127', '128'])).
% 1.58/1.77  thf('130', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k9_setfam_1 @ X12))),
% 1.58/1.77      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.58/1.77  thf('131', plain,
% 1.58/1.77      (![X42 : $i, X43 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ X42)
% 1.58/1.77          | ~ (m1_subset_1 @ X42 @ (k9_setfam_1 @ (u1_struct_0 @ X43)))
% 1.58/1.77          | (m1_pre_topc @ (sk_C_1 @ X42 @ X43) @ X43)
% 1.58/1.77          | ~ (l1_pre_topc @ X43)
% 1.58/1.77          | (v2_struct_0 @ X43))),
% 1.58/1.77      inference('demod', [status(thm)], ['14', '15'])).
% 1.58/1.77  thf('132', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (m1_pre_topc @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['130', '131'])).
% 1.58/1.77  thf('133', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (m1_pre_topc @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['130', '131'])).
% 1.58/1.77  thf('134', plain,
% 1.58/1.77      (![X33 : $i, X34 : $i]:
% 1.58/1.77         (~ (m1_pre_topc @ X33 @ X34)
% 1.58/1.77          | (v1_borsuk_1 @ X33 @ X34)
% 1.58/1.77          | ~ (l1_pre_topc @ X34)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X34)
% 1.58/1.77          | ~ (v2_pre_topc @ X34)
% 1.58/1.77          | (v2_struct_0 @ X34))),
% 1.58/1.77      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 1.58/1.77  thf('135', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v1_borsuk_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0))),
% 1.58/1.77      inference('sup-', [status(thm)], ['133', '134'])).
% 1.58/1.77  thf('136', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v1_borsuk_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.58/1.77      inference('simplify', [status(thm)], ['135'])).
% 1.58/1.77  thf('137', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (m1_pre_topc @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['130', '131'])).
% 1.58/1.77  thf(t1_tsep_1, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( l1_pre_topc @ A ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_pre_topc @ B @ A ) =>
% 1.58/1.77           ( m1_subset_1 @
% 1.58/1.77             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.58/1.77  thf('138', plain,
% 1.58/1.77      (![X30 : $i, X31 : $i]:
% 1.58/1.77         (~ (m1_pre_topc @ X30 @ X31)
% 1.58/1.77          | (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 1.58/1.77             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.58/1.77          | ~ (l1_pre_topc @ X31))),
% 1.58/1.77      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.58/1.77  thf('139', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('140', plain,
% 1.58/1.77      (![X30 : $i, X31 : $i]:
% 1.58/1.77         (~ (m1_pre_topc @ X30 @ X31)
% 1.58/1.77          | (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 1.58/1.77             (k9_setfam_1 @ (u1_struct_0 @ X31)))
% 1.58/1.77          | ~ (l1_pre_topc @ X31))),
% 1.58/1.77      inference('demod', [status(thm)], ['138', '139'])).
% 1.58/1.77  thf('141', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (m1_subset_1 @ 
% 1.58/1.77             (u1_struct_0 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)) @ 
% 1.58/1.77             (k9_setfam_1 @ (u1_struct_0 @ X0))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['137', '140'])).
% 1.58/1.77  thf('142', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((m1_subset_1 @ (u1_struct_0 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)) @ 
% 1.58/1.77           (k9_setfam_1 @ (u1_struct_0 @ X0)))
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.58/1.77      inference('simplify', [status(thm)], ['141'])).
% 1.58/1.77  thf('143', plain,
% 1.58/1.77      (![X27 : $i, X28 : $i]:
% 1.58/1.77         (~ (v2_pre_topc @ X28)
% 1.58/1.77          | ~ (l1_pre_topc @ X28)
% 1.58/1.77          | ~ (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 1.58/1.77               (k9_setfam_1 @ (u1_struct_0 @ X28)))
% 1.58/1.77          | (v4_pre_topc @ (u1_struct_0 @ X27) @ X28)
% 1.58/1.77          | ~ (v1_borsuk_1 @ X27 @ X28)
% 1.58/1.77          | ~ (m1_pre_topc @ X27 @ X28))),
% 1.58/1.77      inference('demod', [status(thm)], ['25', '26'])).
% 1.58/1.77  thf('144', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (m1_pre_topc @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | ~ (v1_borsuk_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | (v4_pre_topc @ 
% 1.58/1.77             (u1_struct_0 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)) @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0))),
% 1.58/1.77      inference('sup-', [status(thm)], ['142', '143'])).
% 1.58/1.77  thf('145', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         (~ (v2_pre_topc @ X0)
% 1.58/1.77          | (v4_pre_topc @ 
% 1.58/1.77             (u1_struct_0 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)) @ X0)
% 1.58/1.77          | ~ (v1_borsuk_1 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | ~ (m1_pre_topc @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.58/1.77      inference('simplify', [status(thm)], ['144'])).
% 1.58/1.77  thf('146', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (m1_pre_topc @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | (v4_pre_topc @ 
% 1.58/1.77             (u1_struct_0 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)) @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0))),
% 1.58/1.77      inference('sup-', [status(thm)], ['136', '145'])).
% 1.58/1.77  thf('147', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v4_pre_topc @ (u1_struct_0 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)) @ 
% 1.58/1.77           X0)
% 1.58/1.77          | ~ (m1_pre_topc @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.58/1.77      inference('simplify', [status(thm)], ['146'])).
% 1.58/1.77  thf('148', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | (v4_pre_topc @ 
% 1.58/1.77             (u1_struct_0 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)) @ X0))),
% 1.58/1.77      inference('sup-', [status(thm)], ['132', '147'])).
% 1.58/1.77  thf('149', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v4_pre_topc @ (u1_struct_0 @ (sk_C_1 @ (u1_struct_0 @ X0) @ X0)) @ 
% 1.58/1.77           X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.58/1.77      inference('simplify', [status(thm)], ['148'])).
% 1.58/1.77  thf('150', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X0))),
% 1.58/1.77      inference('sup+', [status(thm)], ['129', '149'])).
% 1.58/1.77  thf('151', plain,
% 1.58/1.77      (![X0 : $i]:
% 1.58/1.77         (~ (v1_tdlat_3 @ X0)
% 1.58/1.77          | ~ (v2_pre_topc @ X0)
% 1.58/1.77          | (v2_struct_0 @ X0)
% 1.58/1.77          | ~ (l1_pre_topc @ X0)
% 1.58/1.77          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.58/1.77          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 1.58/1.77      inference('simplify', [status(thm)], ['150'])).
% 1.58/1.77  thf('152', plain,
% 1.58/1.77      ((((v4_pre_topc @ sk_B_2 @ sk_A)
% 1.58/1.77         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.58/1.77         | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77         | (v2_struct_0 @ sk_A)
% 1.58/1.77         | ~ (v2_pre_topc @ sk_A)
% 1.58/1.77         | ~ (v1_tdlat_3 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup+', [status(thm)], ['126', '151'])).
% 1.58/1.77  thf('153', plain,
% 1.58/1.77      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['124', '125'])).
% 1.58/1.77  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('156', plain, ((v1_tdlat_3 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('157', plain,
% 1.58/1.77      ((((v4_pre_topc @ sk_B_2 @ sk_A)
% 1.58/1.77         | (v1_xboole_0 @ sk_B_2)
% 1.58/1.77         | (v2_struct_0 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 1.58/1.77  thf('158', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('159', plain,
% 1.58/1.77      ((((v1_xboole_0 @ sk_B_2) | (v4_pre_topc @ sk_B_2 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('clc', [status(thm)], ['157', '158'])).
% 1.58/1.77  thf('160', plain,
% 1.58/1.77      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 1.58/1.77        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('demod', [status(thm)], ['59', '60'])).
% 1.58/1.77  thf('161', plain,
% 1.58/1.77      ((((v1_xboole_0 @ sk_B_2) | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['159', '160'])).
% 1.58/1.77  thf('162', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf('163', plain,
% 1.58/1.77      (![X36 : $i, X37 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.58/1.77          | ((k2_pre_topc @ X37 @ X36) != (u1_struct_0 @ X37))
% 1.58/1.77          | (v1_tops_1 @ X36 @ X37)
% 1.58/1.77          | ~ (l1_pre_topc @ X37))),
% 1.58/1.77      inference('cnf', [status(esa)], [d2_tops_3])).
% 1.58/1.77  thf('164', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('165', plain,
% 1.58/1.77      (![X36 : $i, X37 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X36 @ (k9_setfam_1 @ (u1_struct_0 @ X37)))
% 1.58/1.77          | ((k2_pre_topc @ X37 @ X36) != (u1_struct_0 @ X37))
% 1.58/1.77          | (v1_tops_1 @ X36 @ X37)
% 1.58/1.77          | ~ (l1_pre_topc @ X37))),
% 1.58/1.77      inference('demod', [status(thm)], ['163', '164'])).
% 1.58/1.77  thf('166', plain,
% 1.58/1.77      ((~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | (v1_tops_1 @ sk_B_2 @ sk_A)
% 1.58/1.77        | ((k2_pre_topc @ sk_A @ sk_B_2) != (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['162', '165'])).
% 1.58/1.77  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('168', plain,
% 1.58/1.77      (((v1_tops_1 @ sk_B_2 @ sk_A)
% 1.58/1.77        | ((k2_pre_topc @ sk_A @ sk_B_2) != (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['166', '167'])).
% 1.58/1.77  thf('169', plain,
% 1.58/1.77      (((((sk_B_2) != (u1_struct_0 @ sk_A))
% 1.58/1.77         | (v1_xboole_0 @ sk_B_2)
% 1.58/1.77         | (v1_tops_1 @ sk_B_2 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['161', '168'])).
% 1.58/1.77  thf('170', plain,
% 1.58/1.77      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['124', '125'])).
% 1.58/1.77  thf('171', plain,
% 1.58/1.77      (((((sk_B_2) != (sk_B_2))
% 1.58/1.77         | (v1_xboole_0 @ sk_B_2)
% 1.58/1.77         | (v1_tops_1 @ sk_B_2 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('demod', [status(thm)], ['169', '170'])).
% 1.58/1.77  thf('172', plain,
% 1.58/1.77      ((((v1_tops_1 @ sk_B_2 @ sk_A) | (v1_xboole_0 @ sk_B_2)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('simplify', [status(thm)], ['171'])).
% 1.58/1.77  thf('173', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf(t48_tex_2, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.58/1.77           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 1.58/1.77             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.58/1.77  thf('174', plain,
% 1.58/1.77      (![X52 : $i, X53 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 1.58/1.77          | (v3_tex_2 @ X52 @ X53)
% 1.58/1.77          | ~ (v2_tex_2 @ X52 @ X53)
% 1.58/1.77          | ~ (v1_tops_1 @ X52 @ X53)
% 1.58/1.77          | ~ (l1_pre_topc @ X53)
% 1.58/1.77          | ~ (v2_pre_topc @ X53)
% 1.58/1.77          | (v2_struct_0 @ X53))),
% 1.58/1.77      inference('cnf', [status(esa)], [t48_tex_2])).
% 1.58/1.77  thf('175', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('176', plain,
% 1.58/1.77      (![X52 : $i, X53 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X52 @ (k9_setfam_1 @ (u1_struct_0 @ X53)))
% 1.58/1.77          | (v3_tex_2 @ X52 @ X53)
% 1.58/1.77          | ~ (v2_tex_2 @ X52 @ X53)
% 1.58/1.77          | ~ (v1_tops_1 @ X52 @ X53)
% 1.58/1.77          | ~ (l1_pre_topc @ X53)
% 1.58/1.77          | ~ (v2_pre_topc @ X53)
% 1.58/1.77          | (v2_struct_0 @ X53))),
% 1.58/1.77      inference('demod', [status(thm)], ['174', '175'])).
% 1.58/1.77  thf('177', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (v2_pre_topc @ sk_A)
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | ~ (v1_tops_1 @ sk_B_2 @ sk_A)
% 1.58/1.77        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 1.58/1.77        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('sup-', [status(thm)], ['173', '176'])).
% 1.58/1.77  thf('178', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('180', plain,
% 1.58/1.77      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['2', '3'])).
% 1.58/1.77  thf(t43_tex_2, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 1.58/1.77         ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.58/1.77           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.58/1.77  thf('181', plain,
% 1.58/1.77      (![X46 : $i, X47 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.58/1.77          | (v2_tex_2 @ X46 @ X47)
% 1.58/1.77          | ~ (l1_pre_topc @ X47)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X47)
% 1.58/1.77          | ~ (v2_pre_topc @ X47)
% 1.58/1.77          | (v2_struct_0 @ X47))),
% 1.58/1.77      inference('cnf', [status(esa)], [t43_tex_2])).
% 1.58/1.77  thf('182', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('183', plain,
% 1.58/1.77      (![X46 : $i, X47 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X46 @ (k9_setfam_1 @ (u1_struct_0 @ X47)))
% 1.58/1.77          | (v2_tex_2 @ X46 @ X47)
% 1.58/1.77          | ~ (l1_pre_topc @ X47)
% 1.58/1.77          | ~ (v1_tdlat_3 @ X47)
% 1.58/1.77          | ~ (v2_pre_topc @ X47)
% 1.58/1.77          | (v2_struct_0 @ X47))),
% 1.58/1.77      inference('demod', [status(thm)], ['181', '182'])).
% 1.58/1.77  thf('184', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (v2_pre_topc @ sk_A)
% 1.58/1.77        | ~ (v1_tdlat_3 @ sk_A)
% 1.58/1.77        | ~ (l1_pre_topc @ sk_A)
% 1.58/1.77        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('sup-', [status(thm)], ['180', '183'])).
% 1.58/1.77  thf('185', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('186', plain, ((v1_tdlat_3 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('188', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('demod', [status(thm)], ['184', '185', '186', '187'])).
% 1.58/1.77  thf('189', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('190', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 1.58/1.77      inference('clc', [status(thm)], ['188', '189'])).
% 1.58/1.77  thf('191', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A)
% 1.58/1.77        | ~ (v1_tops_1 @ sk_B_2 @ sk_A)
% 1.58/1.77        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('demod', [status(thm)], ['177', '178', '179', '190'])).
% 1.58/1.77  thf('192', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('193', plain,
% 1.58/1.77      (((v3_tex_2 @ sk_B_2 @ sk_A) | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('clc', [status(thm)], ['191', '192'])).
% 1.58/1.77  thf('194', plain,
% 1.58/1.77      ((((v1_xboole_0 @ sk_B_2) | (v3_tex_2 @ sk_B_2 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['172', '193'])).
% 1.58/1.77  thf('195', plain,
% 1.58/1.77      ((~ (v3_tex_2 @ sk_B_2 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('split', [status(esa)], ['0'])).
% 1.58/1.77  thf('196', plain,
% 1.58/1.77      (((v1_xboole_0 @ sk_B_2))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 1.58/1.77             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['194', '195'])).
% 1.58/1.77  thf(dt_k1_subset_1, axiom,
% 1.58/1.77    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.58/1.77  thf('197', plain,
% 1.58/1.77      (![X11 : $i]: (m1_subset_1 @ (k1_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 1.58/1.77      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 1.58/1.77  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.58/1.77  thf('198', plain, (![X9 : $i]: ((k1_subset_1 @ X9) = (k1_xboole_0))),
% 1.58/1.77      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.58/1.77  thf('199', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('200', plain,
% 1.58/1.77      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X11))),
% 1.58/1.77      inference('demod', [status(thm)], ['197', '198', '199'])).
% 1.58/1.77  thf('201', plain,
% 1.58/1.77      (![X38 : $i, X39 : $i]:
% 1.58/1.77         (((X39) = (X38))
% 1.58/1.77          | (v1_subset_1 @ X39 @ X38)
% 1.58/1.77          | ~ (m1_subset_1 @ X39 @ (k9_setfam_1 @ X38)))),
% 1.58/1.77      inference('demod', [status(thm)], ['121', '122'])).
% 1.58/1.77  thf('202', plain,
% 1.58/1.77      (![X0 : $i]: ((v1_subset_1 @ k1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['200', '201'])).
% 1.58/1.77  thf('203', plain,
% 1.58/1.77      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X11))),
% 1.58/1.77      inference('demod', [status(thm)], ['197', '198', '199'])).
% 1.58/1.77  thf(cc4_subset_1, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( v1_xboole_0 @ A ) =>
% 1.58/1.77       ( ![B:$i]:
% 1.58/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.58/1.77           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 1.58/1.77  thf('204', plain,
% 1.58/1.77      (![X18 : $i, X19 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.58/1.77          | ~ (v1_subset_1 @ X18 @ X19)
% 1.58/1.77          | ~ (v1_xboole_0 @ X19))),
% 1.58/1.77      inference('cnf', [status(esa)], [cc4_subset_1])).
% 1.58/1.77  thf('205', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('206', plain,
% 1.58/1.77      (![X18 : $i, X19 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X18 @ (k9_setfam_1 @ X19))
% 1.58/1.77          | ~ (v1_subset_1 @ X18 @ X19)
% 1.58/1.77          | ~ (v1_xboole_0 @ X19))),
% 1.58/1.77      inference('demod', [status(thm)], ['204', '205'])).
% 1.58/1.77  thf('207', plain,
% 1.58/1.77      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_subset_1 @ k1_xboole_0 @ X0))),
% 1.58/1.77      inference('sup-', [status(thm)], ['203', '206'])).
% 1.58/1.77  thf('208', plain,
% 1.58/1.77      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.58/1.77      inference('sup-', [status(thm)], ['202', '207'])).
% 1.58/1.77  thf('209', plain,
% 1.58/1.77      ((((k1_xboole_0) = (sk_B_2)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 1.58/1.77             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['196', '208'])).
% 1.58/1.77  thf('210', plain,
% 1.58/1.77      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['124', '125'])).
% 1.58/1.77  thf(rc7_pre_topc, axiom,
% 1.58/1.77    (![A:$i]:
% 1.58/1.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.58/1.77       ( ?[B:$i]:
% 1.58/1.77         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.58/1.77           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.58/1.77  thf('211', plain,
% 1.58/1.77      (![X24 : $i]:
% 1.58/1.77         ((m1_subset_1 @ (sk_B @ X24) @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.58/1.77          | ~ (l1_pre_topc @ X24)
% 1.58/1.77          | ~ (v2_pre_topc @ X24)
% 1.58/1.77          | (v2_struct_0 @ X24))),
% 1.58/1.77      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 1.58/1.77  thf('212', plain, (![X20 : $i]: ((k9_setfam_1 @ X20) = (k1_zfmisc_1 @ X20))),
% 1.58/1.77      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 1.58/1.77  thf('213', plain,
% 1.58/1.77      (![X24 : $i]:
% 1.58/1.77         ((m1_subset_1 @ (sk_B @ X24) @ (k9_setfam_1 @ (u1_struct_0 @ X24)))
% 1.58/1.77          | ~ (l1_pre_topc @ X24)
% 1.58/1.77          | ~ (v2_pre_topc @ X24)
% 1.58/1.77          | (v2_struct_0 @ X24))),
% 1.58/1.77      inference('demod', [status(thm)], ['211', '212'])).
% 1.58/1.77  thf('214', plain,
% 1.58/1.77      ((((m1_subset_1 @ (sk_B @ sk_A) @ (k9_setfam_1 @ sk_B_2))
% 1.58/1.77         | (v2_struct_0 @ sk_A)
% 1.58/1.77         | ~ (v2_pre_topc @ sk_A)
% 1.58/1.77         | ~ (l1_pre_topc @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup+', [status(thm)], ['210', '213'])).
% 1.58/1.77  thf('215', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('216', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('217', plain,
% 1.58/1.77      ((((m1_subset_1 @ (sk_B @ sk_A) @ (k9_setfam_1 @ sk_B_2))
% 1.58/1.77         | (v2_struct_0 @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('demod', [status(thm)], ['214', '215', '216'])).
% 1.58/1.77  thf('218', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('219', plain,
% 1.58/1.77      (((m1_subset_1 @ (sk_B @ sk_A) @ (k9_setfam_1 @ sk_B_2)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('clc', [status(thm)], ['217', '218'])).
% 1.58/1.77  thf('220', plain,
% 1.58/1.77      (![X38 : $i, X39 : $i]:
% 1.58/1.77         (((X39) = (X38))
% 1.58/1.77          | (v1_subset_1 @ X39 @ X38)
% 1.58/1.77          | ~ (m1_subset_1 @ X39 @ (k9_setfam_1 @ X38)))),
% 1.58/1.77      inference('demod', [status(thm)], ['121', '122'])).
% 1.58/1.77  thf('221', plain,
% 1.58/1.77      ((((v1_subset_1 @ (sk_B @ sk_A) @ sk_B_2) | ((sk_B @ sk_A) = (sk_B_2))))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['219', '220'])).
% 1.58/1.77  thf('222', plain,
% 1.58/1.77      (((m1_subset_1 @ (sk_B @ sk_A) @ (k9_setfam_1 @ sk_B_2)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('clc', [status(thm)], ['217', '218'])).
% 1.58/1.77  thf('223', plain,
% 1.58/1.77      (![X18 : $i, X19 : $i]:
% 1.58/1.77         (~ (m1_subset_1 @ X18 @ (k9_setfam_1 @ X19))
% 1.58/1.77          | ~ (v1_subset_1 @ X18 @ X19)
% 1.58/1.77          | ~ (v1_xboole_0 @ X19))),
% 1.58/1.77      inference('demod', [status(thm)], ['204', '205'])).
% 1.58/1.77  thf('224', plain,
% 1.58/1.77      (((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_subset_1 @ (sk_B @ sk_A) @ sk_B_2)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['222', '223'])).
% 1.58/1.77  thf('225', plain,
% 1.58/1.77      (((((sk_B @ sk_A) = (sk_B_2)) | ~ (v1_xboole_0 @ sk_B_2)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 1.58/1.77      inference('sup-', [status(thm)], ['221', '224'])).
% 1.58/1.77  thf('226', plain,
% 1.58/1.77      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B @ sk_A) = (sk_B_2))))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 1.58/1.77             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['209', '225'])).
% 1.58/1.77  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.58/1.77  thf('227', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.58/1.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.58/1.77  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.58/1.77  thf('228', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 1.58/1.77      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.58/1.77  thf(t69_xboole_1, axiom,
% 1.58/1.77    (![A:$i,B:$i]:
% 1.58/1.77     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.58/1.77       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.58/1.77  thf('229', plain,
% 1.58/1.77      (![X2 : $i, X3 : $i]:
% 1.58/1.77         (~ (r1_xboole_0 @ X2 @ X3)
% 1.58/1.77          | ~ (r1_tarski @ X2 @ X3)
% 1.58/1.77          | (v1_xboole_0 @ X2))),
% 1.58/1.77      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.58/1.77  thf('230', plain,
% 1.58/1.77      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.58/1.77      inference('sup-', [status(thm)], ['228', '229'])).
% 1.58/1.77  thf('231', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.58/1.77      inference('sup-', [status(thm)], ['227', '230'])).
% 1.58/1.77  thf('232', plain,
% 1.58/1.77      ((((k1_xboole_0) = (sk_B_2)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 1.58/1.77             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['196', '208'])).
% 1.58/1.77  thf('233', plain,
% 1.58/1.77      ((((sk_B @ sk_A) = (k1_xboole_0)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 1.58/1.77             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['226', '231', '232'])).
% 1.58/1.77  thf('234', plain,
% 1.58/1.77      (![X24 : $i]:
% 1.58/1.77         (~ (v1_xboole_0 @ (sk_B @ X24))
% 1.58/1.77          | ~ (l1_pre_topc @ X24)
% 1.58/1.77          | ~ (v2_pre_topc @ X24)
% 1.58/1.77          | (v2_struct_0 @ X24))),
% 1.58/1.77      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 1.58/1.77  thf('235', plain,
% 1.58/1.77      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.58/1.77         | (v2_struct_0 @ sk_A)
% 1.58/1.77         | ~ (v2_pre_topc @ sk_A)
% 1.58/1.77         | ~ (l1_pre_topc @ sk_A)))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 1.58/1.77             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('sup-', [status(thm)], ['233', '234'])).
% 1.58/1.77  thf('236', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.58/1.77      inference('sup-', [status(thm)], ['227', '230'])).
% 1.58/1.77  thf('237', plain, ((v2_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('238', plain, ((l1_pre_topc @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('239', plain,
% 1.58/1.77      (((v2_struct_0 @ sk_A))
% 1.58/1.77         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 1.58/1.77             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 1.58/1.77      inference('demod', [status(thm)], ['235', '236', '237', '238'])).
% 1.58/1.77  thf('240', plain, (~ (v2_struct_0 @ sk_A)),
% 1.58/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.77  thf('241', plain,
% 1.58/1.77      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 1.58/1.77       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 1.58/1.77      inference('sup-', [status(thm)], ['239', '240'])).
% 1.58/1.77  thf('242', plain, ($false),
% 1.58/1.77      inference('sat_resolution*', [status(thm)], ['1', '118', '119', '241'])).
% 1.58/1.77  
% 1.58/1.77  % SZS output end Refutation
% 1.58/1.77  
% 1.58/1.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
