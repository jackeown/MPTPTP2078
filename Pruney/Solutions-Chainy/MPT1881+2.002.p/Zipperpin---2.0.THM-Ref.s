%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.248CEmCejB

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:12 EST 2020

% Result     : Theorem 4.85s
% Output     : Refutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :  300 ( 985 expanded)
%              Number of leaves         :   54 ( 315 expanded)
%              Depth                    :   29
%              Number of atoms          : 2462 (10521 expanded)
%              Number of equality atoms :   80 ( 352 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( X39
        = ( u1_struct_0 @ ( sk_C @ X39 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('6',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('7',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k9_setfam_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( X39
        = ( u1_struct_0 @ ( sk_C @ X39 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X39 @ X40 ) @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('15',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('16',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k9_setfam_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X39 @ X40 ) @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
      <=> ( ( u1_pre_topc @ A )
          = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X32: $i] :
      ( ~ ( v1_tdlat_3 @ X32 )
      | ( ( u1_pre_topc @ X32 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( X26
       != ( u1_struct_0 @ X24 ) )
      | ~ ( v1_borsuk_1 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( v4_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X24 ) @ X25 )
      | ~ ( v1_borsuk_1 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X24 ) @ X25 )
      | ~ ( v1_borsuk_1 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 ) ) ),
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
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ X0 )
      | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
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
    ! [X32: $i] :
      ( ~ ( v1_tdlat_3 @ X32 )
      | ( ( u1_pre_topc @ X32 )
        = ( k9_setfam_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['31','32','33','34','40'])).

thf('42',plain,
    ( ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v1_borsuk_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_tdlat_3 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
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
    | ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('57',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k9_setfam_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( v1_tops_1 @ X47 @ X48 )
      | ~ ( v3_tex_2 @ X47 @ X48 )
      | ~ ( v3_pre_topc @ X47 @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('67',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('68',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k9_setfam_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( v1_tops_1 @ X47 @ X48 )
      | ~ ( v3_tex_2 @ X47 @ X48 )
      | ~ ( v3_pre_topc @ X47 @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 )
      | ( v2_struct_0 @ X48 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_tdlat_3 @ X41 )
      | ( v3_pre_topc @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('74',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('75',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_tdlat_3 @ X41 )
      | ( v3_pre_topc @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k9_setfam_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v1_tops_1 @ X33 @ X34 )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('87',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('88',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k9_setfam_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v1_tops_1 @ X33 @ X34 )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v3_tex_2 @ X45 @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('97',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('98',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k9_setfam_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v3_tex_2 @ X45 @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_subset_1 @ X36 @ X35 )
      | ( X36 != X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('110',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( v1_subset_1 @ X35 @ X35 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('112',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k9_setfam_1 @ X35 ) )
      | ~ ( v1_subset_1 @ X35 @ X35 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('113',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('114',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('115',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('116',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k9_setfam_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X35: $i] :
      ~ ( v1_subset_1 @ X35 @ X35 ) ),
    inference(demod,[status(thm)],['112','116'])).

thf('118',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','117'])).

thf('119',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('120',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('121',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('122',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 = X35 )
      | ( v1_subset_1 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('123',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('124',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 = X35 )
      | ( v1_subset_1 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k9_setfam_1 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['63'])).

thf('127',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k9_setfam_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('129',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k9_setfam_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X39 @ X40 ) @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('132',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v1_borsuk_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v1_tdlat_3 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_borsuk_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v1_borsuk_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('136',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('137',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('138',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X24 ) @ X25 )
      | ~ ( v1_borsuk_1 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_borsuk_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( v1_borsuk_1 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( m1_pre_topc @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ ( u1_struct_0 @ X0 ) @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['127','147'])).

thf('149',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152'])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( v4_pre_topc @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['120','155'])).

thf('157',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v4_pre_topc @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
        = sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_B_2 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('161',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
       != ( u1_struct_0 @ X34 ) )
      | ( v1_tops_1 @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('162',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('163',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k9_setfam_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
       != ( u1_struct_0 @ X34 ) )
      | ( v1_tops_1 @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( sk_B_2
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_tops_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','166'])).

thf('168',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('169',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_tops_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( v1_tops_1 @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
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

thf('172',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( v3_tex_2 @ X49 @ X50 )
      | ~ ( v2_tex_2 @ X49 @ X50 )
      | ~ ( v1_tops_1 @ X49 @ X50 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('173',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('174',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k9_setfam_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( v3_tex_2 @ X49 @ X50 )
      | ~ ( v2_tex_2 @ X49 @ X50 )
      | ~ ( v1_tops_1 @ X49 @ X50 )
      | ~ ( l1_pre_topc @ X50 )
      | ~ ( v2_pre_topc @ X50 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['171','174'])).

thf('176',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
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

thf('179',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v2_tex_2 @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_tdlat_3 @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('180',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('181',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k9_setfam_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v2_tex_2 @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_tdlat_3 @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['175','176','177','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v3_tex_2 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','191'])).

thf('193',plain,
    ( ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('194',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('195',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('196',plain,(
    ! [X3: $i] :
      ( ( k1_subset_1 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('197',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('198',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 = X35 )
      | ( v1_subset_1 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k9_setfam_1 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('202',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( v1_subset_1 @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('203',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('204',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k9_setfam_1 @ X13 ) )
      | ~ ( v1_subset_1 @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['201','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['200','205'])).

thf('207',plain,
    ( ( k1_xboole_0 = sk_B_2 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','206'])).

thf('208',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('209',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('210',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('211',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X23 ) @ ( k9_setfam_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,
    ( ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k9_setfam_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['208','211'])).

thf('213',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k9_setfam_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k9_setfam_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 = X35 )
      | ( v1_subset_1 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k9_setfam_1 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('219',plain,
    ( ( ( v1_subset_1 @ ( sk_B @ sk_A ) @ sk_B_2 )
      | ( ( sk_B @ sk_A )
        = sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k9_setfam_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('221',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k9_setfam_1 @ X13 ) )
      | ~ ( v1_subset_1 @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('222',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_subset_1 @ ( sk_B @ sk_A ) @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( ( ( sk_B @ sk_A )
        = sk_B_2 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['219','222'])).

thf('224',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = sk_B_2 ) )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['207','223'])).

thf('225',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k9_setfam_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('226',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('227',plain,(
    ! [X17: $i] :
      ( ( k9_setfam_1 @ X17 )
      = ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('228',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k9_setfam_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['225','228'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('230',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('231',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['229','232'])).

thf('234',plain,
    ( ( k1_xboole_0 = sk_B_2 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['194','206'])).

thf('235',plain,
    ( ( ( sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['224','233','234'])).

thf('236',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('237',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['229','232'])).

thf('239',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['237','238','239','240'])).

thf('242',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','118','119','243'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.248CEmCejB
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.85/5.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.85/5.06  % Solved by: fo/fo7.sh
% 4.85/5.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.85/5.06  % done 4013 iterations in 4.575s
% 4.85/5.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.85/5.06  % SZS output start Refutation
% 4.85/5.06  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 4.85/5.06  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 4.85/5.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.85/5.06  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 4.85/5.06  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.85/5.06  thf(sk_A_type, type, sk_A: $i).
% 4.85/5.06  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 4.85/5.06  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 4.85/5.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.85/5.06  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 4.85/5.06  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.85/5.06  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 4.85/5.06  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.85/5.06  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 4.85/5.06  thf(sk_B_2_type, type, sk_B_2: $i).
% 4.85/5.06  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 4.85/5.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.85/5.06  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 4.85/5.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.85/5.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.85/5.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.85/5.06  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 4.85/5.06  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.85/5.06  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 4.85/5.06  thf(sk_B_type, type, sk_B: $i > $i).
% 4.85/5.06  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 4.85/5.06  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 4.85/5.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.85/5.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.85/5.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.85/5.06  thf(t49_tex_2, conjecture,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 4.85/5.06         ( l1_pre_topc @ A ) ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.85/5.06           ( ( v3_tex_2 @ B @ A ) <=>
% 4.85/5.06             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 4.85/5.06  thf(zf_stmt_0, negated_conjecture,
% 4.85/5.06    (~( ![A:$i]:
% 4.85/5.06        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.85/5.06            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.85/5.06          ( ![B:$i]:
% 4.85/5.06            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.85/5.06              ( ( v3_tex_2 @ B @ A ) <=>
% 4.85/5.06                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 4.85/5.06    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 4.85/5.06  thf('0', plain,
% 4.85/5.06      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 4.85/5.06        | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('1', plain,
% 4.85/5.06      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 4.85/5.06       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('split', [status(esa)], ['0'])).
% 4.85/5.06  thf('2', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf(redefinition_k9_setfam_1, axiom,
% 4.85/5.06    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 4.85/5.06  thf('3', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('4', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf(t10_tsep_1, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 4.85/5.06             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.85/5.06           ( ?[C:$i]:
% 4.85/5.06             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 4.85/5.06               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 4.85/5.06  thf('5', plain,
% 4.85/5.06      (![X39 : $i, X40 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ X39)
% 4.85/5.06          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 4.85/5.06          | ((X39) = (u1_struct_0 @ (sk_C @ X39 @ X40)))
% 4.85/5.06          | ~ (l1_pre_topc @ X40)
% 4.85/5.06          | (v2_struct_0 @ X40))),
% 4.85/5.06      inference('cnf', [status(esa)], [t10_tsep_1])).
% 4.85/5.06  thf('6', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('7', plain,
% 4.85/5.06      (![X39 : $i, X40 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ X39)
% 4.85/5.06          | ~ (m1_subset_1 @ X39 @ (k9_setfam_1 @ (u1_struct_0 @ X40)))
% 4.85/5.06          | ((X39) = (u1_struct_0 @ (sk_C @ X39 @ X40)))
% 4.85/5.06          | ~ (l1_pre_topc @ X40)
% 4.85/5.06          | (v2_struct_0 @ X40))),
% 4.85/5.06      inference('demod', [status(thm)], ['5', '6'])).
% 4.85/5.06  thf('8', plain,
% 4.85/5.06      (((v2_struct_0 @ sk_A)
% 4.85/5.06        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)))
% 4.85/5.06        | (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('sup-', [status(thm)], ['4', '7'])).
% 4.85/5.06  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('10', plain,
% 4.85/5.06      (((v2_struct_0 @ sk_A)
% 4.85/5.06        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)))
% 4.85/5.06        | (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('demod', [status(thm)], ['8', '9'])).
% 4.85/5.06  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('12', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A))))),
% 4.85/5.06      inference('clc', [status(thm)], ['10', '11'])).
% 4.85/5.06  thf('13', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf('14', plain,
% 4.85/5.06      (![X39 : $i, X40 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ X39)
% 4.85/5.06          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 4.85/5.06          | (m1_pre_topc @ (sk_C @ X39 @ X40) @ X40)
% 4.85/5.06          | ~ (l1_pre_topc @ X40)
% 4.85/5.06          | (v2_struct_0 @ X40))),
% 4.85/5.06      inference('cnf', [status(esa)], [t10_tsep_1])).
% 4.85/5.06  thf('15', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('16', plain,
% 4.85/5.06      (![X39 : $i, X40 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ X39)
% 4.85/5.06          | ~ (m1_subset_1 @ X39 @ (k9_setfam_1 @ (u1_struct_0 @ X40)))
% 4.85/5.06          | (m1_pre_topc @ (sk_C @ X39 @ X40) @ X40)
% 4.85/5.06          | ~ (l1_pre_topc @ X40)
% 4.85/5.06          | (v2_struct_0 @ X40))),
% 4.85/5.06      inference('demod', [status(thm)], ['14', '15'])).
% 4.85/5.06  thf('17', plain,
% 4.85/5.06      (((v2_struct_0 @ sk_A)
% 4.85/5.06        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 4.85/5.06        | (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('sup-', [status(thm)], ['13', '16'])).
% 4.85/5.06  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('19', plain,
% 4.85/5.06      (((v2_struct_0 @ sk_A)
% 4.85/5.06        | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 4.85/5.06        | (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('demod', [status(thm)], ['17', '18'])).
% 4.85/5.06  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('21', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2) | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 4.85/5.06      inference('clc', [status(thm)], ['19', '20'])).
% 4.85/5.06  thf('22', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A))))),
% 4.85/5.06      inference('clc', [status(thm)], ['10', '11'])).
% 4.85/5.06  thf(d1_tdlat_3, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( l1_pre_topc @ A ) =>
% 4.85/5.06       ( ( v1_tdlat_3 @ A ) <=>
% 4.85/5.06         ( ( u1_pre_topc @ A ) = ( k9_setfam_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 4.85/5.06  thf('23', plain,
% 4.85/5.06      (![X32 : $i]:
% 4.85/5.06         (~ (v1_tdlat_3 @ X32)
% 4.85/5.06          | ((u1_pre_topc @ X32) = (k9_setfam_1 @ (u1_struct_0 @ X32)))
% 4.85/5.06          | ~ (l1_pre_topc @ X32))),
% 4.85/5.06      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 4.85/5.06  thf(t11_tsep_1, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( m1_pre_topc @ B @ A ) =>
% 4.85/5.06           ( ![C:$i]:
% 4.85/5.06             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.85/5.06               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 4.85/5.06                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 4.85/5.06                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 4.85/5.06  thf('24', plain,
% 4.85/5.06      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.85/5.06         (~ (m1_pre_topc @ X24 @ X25)
% 4.85/5.06          | ((X26) != (u1_struct_0 @ X24))
% 4.85/5.06          | ~ (v1_borsuk_1 @ X24 @ X25)
% 4.85/5.06          | ~ (m1_pre_topc @ X24 @ X25)
% 4.85/5.06          | (v4_pre_topc @ X26 @ X25)
% 4.85/5.06          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 4.85/5.06          | ~ (l1_pre_topc @ X25)
% 4.85/5.06          | ~ (v2_pre_topc @ X25))),
% 4.85/5.06      inference('cnf', [status(esa)], [t11_tsep_1])).
% 4.85/5.06  thf('25', plain,
% 4.85/5.06      (![X24 : $i, X25 : $i]:
% 4.85/5.06         (~ (v2_pre_topc @ X25)
% 4.85/5.06          | ~ (l1_pre_topc @ X25)
% 4.85/5.06          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 4.85/5.06               (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ X24) @ X25)
% 4.85/5.06          | ~ (v1_borsuk_1 @ X24 @ X25)
% 4.85/5.06          | ~ (m1_pre_topc @ X24 @ X25))),
% 4.85/5.06      inference('simplify', [status(thm)], ['24'])).
% 4.85/5.06  thf('26', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('27', plain,
% 4.85/5.06      (![X24 : $i, X25 : $i]:
% 4.85/5.06         (~ (v2_pre_topc @ X25)
% 4.85/5.06          | ~ (l1_pre_topc @ X25)
% 4.85/5.06          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 4.85/5.06               (k9_setfam_1 @ (u1_struct_0 @ X25)))
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ X24) @ X25)
% 4.85/5.06          | ~ (v1_borsuk_1 @ X24 @ X25)
% 4.85/5.06          | ~ (m1_pre_topc @ X24 @ X25))),
% 4.85/5.06      inference('demod', [status(thm)], ['25', '26'])).
% 4.85/5.06  thf('28', plain,
% 4.85/5.06      (![X0 : $i, X1 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X0))
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X0)
% 4.85/5.06          | ~ (m1_pre_topc @ X1 @ X0)
% 4.85/5.06          | ~ (v1_borsuk_1 @ X1 @ X0)
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ X1) @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0))),
% 4.85/5.06      inference('sup-', [status(thm)], ['23', '27'])).
% 4.85/5.06  thf('29', plain,
% 4.85/5.06      (![X0 : $i, X1 : $i]:
% 4.85/5.06         (~ (v2_pre_topc @ X0)
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ X1) @ X0)
% 4.85/5.06          | ~ (v1_borsuk_1 @ X1 @ X0)
% 4.85/5.06          | ~ (m1_pre_topc @ X1 @ X0)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | ~ (m1_subset_1 @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X0)))),
% 4.85/5.06      inference('simplify', [status(thm)], ['28'])).
% 4.85/5.06  thf('30', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ sk_B_2 @ (u1_pre_topc @ X0))
% 4.85/5.06          | (v1_xboole_0 @ sk_B_2)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X0)
% 4.85/5.06          | ~ (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ X0)
% 4.85/5.06          | ~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ X0)
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0))),
% 4.85/5.06      inference('sup-', [status(thm)], ['22', '29'])).
% 4.85/5.06  thf('31', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | ~ (v2_pre_topc @ sk_A)
% 4.85/5.06        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 4.85/5.06        | ~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 4.85/5.06        | ~ (v1_tdlat_3 @ sk_A)
% 4.85/5.06        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | (v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | ~ (m1_subset_1 @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['21', '30'])).
% 4.85/5.06  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('33', plain, ((v1_tdlat_3 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('35', plain,
% 4.85/5.06      (![X32 : $i]:
% 4.85/5.06         (~ (v1_tdlat_3 @ X32)
% 4.85/5.06          | ((u1_pre_topc @ X32) = (k9_setfam_1 @ (u1_struct_0 @ X32)))
% 4.85/5.06          | ~ (l1_pre_topc @ X32))),
% 4.85/5.06      inference('cnf', [status(esa)], [d1_tdlat_3])).
% 4.85/5.06  thf('36', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf('37', plain,
% 4.85/5.06      (((m1_subset_1 @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 4.85/5.06        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | ~ (v1_tdlat_3 @ sk_A))),
% 4.85/5.06      inference('sup+', [status(thm)], ['35', '36'])).
% 4.85/5.06  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('39', plain, ((v1_tdlat_3 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('40', plain, ((m1_subset_1 @ sk_B_2 @ (u1_pre_topc @ sk_A))),
% 4.85/5.06      inference('demod', [status(thm)], ['37', '38', '39'])).
% 4.85/5.06  thf('41', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 4.85/5.06        | ~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 4.85/5.06        | (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('demod', [status(thm)], ['31', '32', '33', '34', '40'])).
% 4.85/5.06  thf('42', plain,
% 4.85/5.06      ((~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 4.85/5.06        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 4.85/5.06        | (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('simplify', [status(thm)], ['41'])).
% 4.85/5.06  thf('43', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2) | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 4.85/5.06      inference('clc', [status(thm)], ['19', '20'])).
% 4.85/5.06  thf(cc5_tdlat_3, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 4.85/5.06         ( l1_pre_topc @ A ) ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( m1_pre_topc @ B @ A ) =>
% 4.85/5.06           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 4.85/5.06             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 4.85/5.06  thf('44', plain,
% 4.85/5.06      (![X30 : $i, X31 : $i]:
% 4.85/5.06         (~ (m1_pre_topc @ X30 @ X31)
% 4.85/5.06          | (v1_borsuk_1 @ X30 @ X31)
% 4.85/5.06          | ~ (l1_pre_topc @ X31)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X31)
% 4.85/5.06          | ~ (v2_pre_topc @ X31)
% 4.85/5.06          | (v2_struct_0 @ X31))),
% 4.85/5.06      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 4.85/5.06  thf('45', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | (v2_struct_0 @ sk_A)
% 4.85/5.06        | ~ (v2_pre_topc @ sk_A)
% 4.85/5.06        | ~ (v1_tdlat_3 @ sk_A)
% 4.85/5.06        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 4.85/5.06      inference('sup-', [status(thm)], ['43', '44'])).
% 4.85/5.06  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('47', plain, ((v1_tdlat_3 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('49', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | (v2_struct_0 @ sk_A)
% 4.85/5.06        | (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 4.85/5.06      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 4.85/5.06  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('51', plain,
% 4.85/5.06      (((v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A) | (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('clc', [status(thm)], ['49', '50'])).
% 4.85/5.06  thf('52', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A))),
% 4.85/5.06      inference('clc', [status(thm)], ['42', '51'])).
% 4.85/5.06  thf('53', plain,
% 4.85/5.06      (((v4_pre_topc @ sk_B_2 @ sk_A)
% 4.85/5.06        | (v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('sup+', [status(thm)], ['12', '52'])).
% 4.85/5.06  thf('54', plain, (((v1_xboole_0 @ sk_B_2) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('simplify', [status(thm)], ['53'])).
% 4.85/5.06  thf('55', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf(t52_pre_topc, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( l1_pre_topc @ A ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.85/5.06           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 4.85/5.06             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 4.85/5.06               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 4.85/5.06  thf('56', plain,
% 4.85/5.06      (![X21 : $i, X22 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 4.85/5.06          | ~ (v4_pre_topc @ X21 @ X22)
% 4.85/5.06          | ((k2_pre_topc @ X22 @ X21) = (X21))
% 4.85/5.06          | ~ (l1_pre_topc @ X22))),
% 4.85/5.06      inference('cnf', [status(esa)], [t52_pre_topc])).
% 4.85/5.06  thf('57', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('58', plain,
% 4.85/5.06      (![X21 : $i, X22 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X21 @ (k9_setfam_1 @ (u1_struct_0 @ X22)))
% 4.85/5.06          | ~ (v4_pre_topc @ X21 @ X22)
% 4.85/5.06          | ((k2_pre_topc @ X22 @ X21) = (X21))
% 4.85/5.06          | ~ (l1_pre_topc @ X22))),
% 4.85/5.06      inference('demod', [status(thm)], ['56', '57'])).
% 4.85/5.06  thf('59', plain,
% 4.85/5.06      ((~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 4.85/5.06        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('sup-', [status(thm)], ['55', '58'])).
% 4.85/5.06  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('61', plain,
% 4.85/5.06      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 4.85/5.06        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('demod', [status(thm)], ['59', '60'])).
% 4.85/5.06  thf('62', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2) | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['54', '61'])).
% 4.85/5.06  thf('63', plain,
% 4.85/5.06      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 4.85/5.06        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('64', plain,
% 4.85/5.06      (((v3_tex_2 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.06      inference('split', [status(esa)], ['63'])).
% 4.85/5.06  thf('65', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf(t47_tex_2, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.85/5.06           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 4.85/5.06             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 4.85/5.06  thf('66', plain,
% 4.85/5.06      (![X47 : $i, X48 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 4.85/5.06          | (v1_tops_1 @ X47 @ X48)
% 4.85/5.06          | ~ (v3_tex_2 @ X47 @ X48)
% 4.85/5.06          | ~ (v3_pre_topc @ X47 @ X48)
% 4.85/5.06          | ~ (l1_pre_topc @ X48)
% 4.85/5.06          | ~ (v2_pre_topc @ X48)
% 4.85/5.06          | (v2_struct_0 @ X48))),
% 4.85/5.06      inference('cnf', [status(esa)], [t47_tex_2])).
% 4.85/5.06  thf('67', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('68', plain,
% 4.85/5.06      (![X47 : $i, X48 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X47 @ (k9_setfam_1 @ (u1_struct_0 @ X48)))
% 4.85/5.06          | (v1_tops_1 @ X47 @ X48)
% 4.85/5.06          | ~ (v3_tex_2 @ X47 @ X48)
% 4.85/5.06          | ~ (v3_pre_topc @ X47 @ X48)
% 4.85/5.06          | ~ (l1_pre_topc @ X48)
% 4.85/5.06          | ~ (v2_pre_topc @ X48)
% 4.85/5.06          | (v2_struct_0 @ X48))),
% 4.85/5.06      inference('demod', [status(thm)], ['66', '67'])).
% 4.85/5.06  thf('69', plain,
% 4.85/5.06      (((v2_struct_0 @ sk_A)
% 4.85/5.06        | ~ (v2_pre_topc @ sk_A)
% 4.85/5.06        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 4.85/5.06        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 4.85/5.06        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('sup-', [status(thm)], ['65', '68'])).
% 4.85/5.06  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('72', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf(t17_tdlat_3, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.85/5.06       ( ( v1_tdlat_3 @ A ) <=>
% 4.85/5.06         ( ![B:$i]:
% 4.85/5.06           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.85/5.06             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 4.85/5.06  thf('73', plain,
% 4.85/5.06      (![X41 : $i, X42 : $i]:
% 4.85/5.06         (~ (v1_tdlat_3 @ X41)
% 4.85/5.06          | (v3_pre_topc @ X42 @ X41)
% 4.85/5.06          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 4.85/5.06          | ~ (l1_pre_topc @ X41)
% 4.85/5.06          | ~ (v2_pre_topc @ X41))),
% 4.85/5.06      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 4.85/5.06  thf('74', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('75', plain,
% 4.85/5.06      (![X41 : $i, X42 : $i]:
% 4.85/5.06         (~ (v1_tdlat_3 @ X41)
% 4.85/5.06          | (v3_pre_topc @ X42 @ X41)
% 4.85/5.06          | ~ (m1_subset_1 @ X42 @ (k9_setfam_1 @ (u1_struct_0 @ X41)))
% 4.85/5.06          | ~ (l1_pre_topc @ X41)
% 4.85/5.06          | ~ (v2_pre_topc @ X41))),
% 4.85/5.06      inference('demod', [status(thm)], ['73', '74'])).
% 4.85/5.06  thf('76', plain,
% 4.85/5.06      ((~ (v2_pre_topc @ sk_A)
% 4.85/5.06        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 4.85/5.06        | ~ (v1_tdlat_3 @ sk_A))),
% 4.85/5.06      inference('sup-', [status(thm)], ['72', '75'])).
% 4.85/5.06  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('79', plain, ((v1_tdlat_3 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('80', plain, ((v3_pre_topc @ sk_B_2 @ sk_A)),
% 4.85/5.06      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 4.85/5.06  thf('81', plain,
% 4.85/5.06      (((v2_struct_0 @ sk_A)
% 4.85/5.06        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 4.85/5.06        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('demod', [status(thm)], ['69', '70', '71', '80'])).
% 4.85/5.06  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('83', plain,
% 4.85/5.06      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('clc', [status(thm)], ['81', '82'])).
% 4.85/5.06  thf('84', plain,
% 4.85/5.06      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['64', '83'])).
% 4.85/5.06  thf('85', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf(d2_tops_3, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( l1_pre_topc @ A ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.85/5.06           ( ( v1_tops_1 @ B @ A ) <=>
% 4.85/5.06             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.85/5.06  thf('86', plain,
% 4.85/5.06      (![X33 : $i, X34 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 4.85/5.06          | ~ (v1_tops_1 @ X33 @ X34)
% 4.85/5.06          | ((k2_pre_topc @ X34 @ X33) = (u1_struct_0 @ X34))
% 4.85/5.06          | ~ (l1_pre_topc @ X34))),
% 4.85/5.06      inference('cnf', [status(esa)], [d2_tops_3])).
% 4.85/5.06  thf('87', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('88', plain,
% 4.85/5.06      (![X33 : $i, X34 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X33 @ (k9_setfam_1 @ (u1_struct_0 @ X34)))
% 4.85/5.06          | ~ (v1_tops_1 @ X33 @ X34)
% 4.85/5.06          | ((k2_pre_topc @ X34 @ X33) = (u1_struct_0 @ X34))
% 4.85/5.06          | ~ (l1_pre_topc @ X34))),
% 4.85/5.06      inference('demod', [status(thm)], ['86', '87'])).
% 4.85/5.06  thf('89', plain,
% 4.85/5.06      ((~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 4.85/5.06        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('sup-', [status(thm)], ['85', '88'])).
% 4.85/5.06  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('91', plain,
% 4.85/5.06      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 4.85/5.06        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('demod', [status(thm)], ['89', '90'])).
% 4.85/5.06  thf('92', plain,
% 4.85/5.06      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 4.85/5.06         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['84', '91'])).
% 4.85/5.06  thf('93', plain,
% 4.85/5.06      (((((sk_B_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_2)))
% 4.85/5.06         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.06      inference('sup+', [status(thm)], ['62', '92'])).
% 4.85/5.06  thf('94', plain,
% 4.85/5.06      (((v3_tex_2 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.06      inference('split', [status(esa)], ['63'])).
% 4.85/5.06  thf('95', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf(t46_tex_2, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( ( v1_xboole_0 @ B ) & 
% 4.85/5.06             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.85/5.06           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 4.85/5.06  thf('96', plain,
% 4.85/5.06      (![X45 : $i, X46 : $i]:
% 4.85/5.06         (~ (v1_xboole_0 @ X45)
% 4.85/5.06          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 4.85/5.06          | ~ (v3_tex_2 @ X45 @ X46)
% 4.85/5.06          | ~ (l1_pre_topc @ X46)
% 4.85/5.06          | ~ (v2_pre_topc @ X46)
% 4.85/5.06          | (v2_struct_0 @ X46))),
% 4.85/5.06      inference('cnf', [status(esa)], [t46_tex_2])).
% 4.85/5.06  thf('97', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('98', plain,
% 4.85/5.06      (![X45 : $i, X46 : $i]:
% 4.85/5.06         (~ (v1_xboole_0 @ X45)
% 4.85/5.06          | ~ (m1_subset_1 @ X45 @ (k9_setfam_1 @ (u1_struct_0 @ X46)))
% 4.85/5.06          | ~ (v3_tex_2 @ X45 @ X46)
% 4.85/5.06          | ~ (l1_pre_topc @ X46)
% 4.85/5.06          | ~ (v2_pre_topc @ X46)
% 4.85/5.06          | (v2_struct_0 @ X46))),
% 4.85/5.06      inference('demod', [status(thm)], ['96', '97'])).
% 4.85/5.06  thf('99', plain,
% 4.85/5.06      (((v2_struct_0 @ sk_A)
% 4.85/5.06        | ~ (v2_pre_topc @ sk_A)
% 4.85/5.06        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 4.85/5.06        | ~ (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('sup-', [status(thm)], ['95', '98'])).
% 4.85/5.06  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('102', plain,
% 4.85/5.06      (((v2_struct_0 @ sk_A)
% 4.85/5.06        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 4.85/5.06        | ~ (v1_xboole_0 @ sk_B_2))),
% 4.85/5.06      inference('demod', [status(thm)], ['99', '100', '101'])).
% 4.85/5.06  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('104', plain,
% 4.85/5.06      ((~ (v1_xboole_0 @ sk_B_2) | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('clc', [status(thm)], ['102', '103'])).
% 4.85/5.06  thf('105', plain,
% 4.85/5.06      ((~ (v1_xboole_0 @ sk_B_2)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['94', '104'])).
% 4.85/5.06  thf('106', plain,
% 4.85/5.06      ((((sk_B_2) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.06      inference('clc', [status(thm)], ['93', '105'])).
% 4.85/5.06  thf('107', plain,
% 4.85/5.06      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 4.85/5.06         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('split', [status(esa)], ['0'])).
% 4.85/5.06  thf('108', plain,
% 4.85/5.06      (((v1_subset_1 @ sk_B_2 @ sk_B_2))
% 4.85/5.06         <= (((v3_tex_2 @ sk_B_2 @ sk_A)) & 
% 4.85/5.06             ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('sup+', [status(thm)], ['106', '107'])).
% 4.85/5.06  thf(d7_subset_1, axiom,
% 4.85/5.06    (![A:$i,B:$i]:
% 4.85/5.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.85/5.06       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 4.85/5.06  thf('109', plain,
% 4.85/5.06      (![X35 : $i, X36 : $i]:
% 4.85/5.06         (~ (v1_subset_1 @ X36 @ X35)
% 4.85/5.06          | ((X36) != (X35))
% 4.85/5.06          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 4.85/5.06      inference('cnf', [status(esa)], [d7_subset_1])).
% 4.85/5.06  thf('110', plain,
% 4.85/5.06      (![X35 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X35))
% 4.85/5.06          | ~ (v1_subset_1 @ X35 @ X35))),
% 4.85/5.06      inference('simplify', [status(thm)], ['109'])).
% 4.85/5.06  thf('111', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('112', plain,
% 4.85/5.06      (![X35 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X35 @ (k9_setfam_1 @ X35))
% 4.85/5.06          | ~ (v1_subset_1 @ X35 @ X35))),
% 4.85/5.06      inference('demod', [status(thm)], ['110', '111'])).
% 4.85/5.06  thf(dt_k2_subset_1, axiom,
% 4.85/5.06    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 4.85/5.06  thf('113', plain,
% 4.85/5.06      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 4.85/5.06      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 4.85/5.06  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 4.85/5.06  thf('114', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 4.85/5.06      inference('cnf', [status(esa)], [d4_subset_1])).
% 4.85/5.06  thf('115', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('116', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k9_setfam_1 @ X6))),
% 4.85/5.06      inference('demod', [status(thm)], ['113', '114', '115'])).
% 4.85/5.06  thf('117', plain, (![X35 : $i]: ~ (v1_subset_1 @ X35 @ X35)),
% 4.85/5.06      inference('demod', [status(thm)], ['112', '116'])).
% 4.85/5.06  thf('118', plain,
% 4.85/5.06      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 4.85/5.06       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('sup-', [status(thm)], ['108', '117'])).
% 4.85/5.06  thf('119', plain,
% 4.85/5.06      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 4.85/5.06       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('split', [status(esa)], ['63'])).
% 4.85/5.06  thf('120', plain,
% 4.85/5.06      (((v1_xboole_0 @ sk_B_2)
% 4.85/5.06        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A))))),
% 4.85/5.06      inference('clc', [status(thm)], ['10', '11'])).
% 4.85/5.06  thf('121', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf('122', plain,
% 4.85/5.06      (![X35 : $i, X36 : $i]:
% 4.85/5.06         (((X36) = (X35))
% 4.85/5.06          | (v1_subset_1 @ X36 @ X35)
% 4.85/5.06          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 4.85/5.06      inference('cnf', [status(esa)], [d7_subset_1])).
% 4.85/5.06  thf('123', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('124', plain,
% 4.85/5.06      (![X35 : $i, X36 : $i]:
% 4.85/5.06         (((X36) = (X35))
% 4.85/5.06          | (v1_subset_1 @ X36 @ X35)
% 4.85/5.06          | ~ (m1_subset_1 @ X36 @ (k9_setfam_1 @ X35)))),
% 4.85/5.06      inference('demod', [status(thm)], ['122', '123'])).
% 4.85/5.06  thf('125', plain,
% 4.85/5.06      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 4.85/5.06        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['121', '124'])).
% 4.85/5.06  thf('126', plain,
% 4.85/5.06      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('split', [status(esa)], ['63'])).
% 4.85/5.06  thf('127', plain,
% 4.85/5.06      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('sup-', [status(thm)], ['125', '126'])).
% 4.85/5.06  thf('128', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k9_setfam_1 @ X6))),
% 4.85/5.06      inference('demod', [status(thm)], ['113', '114', '115'])).
% 4.85/5.06  thf('129', plain,
% 4.85/5.06      (![X39 : $i, X40 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ X39)
% 4.85/5.06          | ~ (m1_subset_1 @ X39 @ (k9_setfam_1 @ (u1_struct_0 @ X40)))
% 4.85/5.06          | (m1_pre_topc @ (sk_C @ X39 @ X40) @ X40)
% 4.85/5.06          | ~ (l1_pre_topc @ X40)
% 4.85/5.06          | (v2_struct_0 @ X40))),
% 4.85/5.06      inference('demod', [status(thm)], ['14', '15'])).
% 4.85/5.06  thf('130', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v2_struct_0 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (m1_pre_topc @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['128', '129'])).
% 4.85/5.06  thf('131', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v2_struct_0 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (m1_pre_topc @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['128', '129'])).
% 4.85/5.06  thf('132', plain,
% 4.85/5.06      (![X30 : $i, X31 : $i]:
% 4.85/5.06         (~ (m1_pre_topc @ X30 @ X31)
% 4.85/5.06          | (v1_borsuk_1 @ X30 @ X31)
% 4.85/5.06          | ~ (l1_pre_topc @ X31)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X31)
% 4.85/5.06          | ~ (v2_pre_topc @ X31)
% 4.85/5.06          | (v2_struct_0 @ X31))),
% 4.85/5.06      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 4.85/5.06  thf('133', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v1_borsuk_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0))),
% 4.85/5.06      inference('sup-', [status(thm)], ['131', '132'])).
% 4.85/5.06  thf('134', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v1_borsuk_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 4.85/5.06      inference('simplify', [status(thm)], ['133'])).
% 4.85/5.06  thf('135', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v2_struct_0 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (m1_pre_topc @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['128', '129'])).
% 4.85/5.06  thf(t1_tsep_1, axiom,
% 4.85/5.06    (![A:$i]:
% 4.85/5.06     ( ( l1_pre_topc @ A ) =>
% 4.85/5.06       ( ![B:$i]:
% 4.85/5.06         ( ( m1_pre_topc @ B @ A ) =>
% 4.85/5.06           ( m1_subset_1 @
% 4.85/5.06             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.85/5.06  thf('136', plain,
% 4.85/5.06      (![X27 : $i, X28 : $i]:
% 4.85/5.06         (~ (m1_pre_topc @ X27 @ X28)
% 4.85/5.06          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 4.85/5.06             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 4.85/5.06          | ~ (l1_pre_topc @ X28))),
% 4.85/5.06      inference('cnf', [status(esa)], [t1_tsep_1])).
% 4.85/5.06  thf('137', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('138', plain,
% 4.85/5.06      (![X27 : $i, X28 : $i]:
% 4.85/5.06         (~ (m1_pre_topc @ X27 @ X28)
% 4.85/5.06          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 4.85/5.06             (k9_setfam_1 @ (u1_struct_0 @ X28)))
% 4.85/5.06          | ~ (l1_pre_topc @ X28))),
% 4.85/5.06      inference('demod', [status(thm)], ['136', '137'])).
% 4.85/5.06  thf('139', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (m1_subset_1 @ (u1_struct_0 @ (sk_C @ (u1_struct_0 @ X0) @ X0)) @ 
% 4.85/5.06             (k9_setfam_1 @ (u1_struct_0 @ X0))))),
% 4.85/5.06      inference('sup-', [status(thm)], ['135', '138'])).
% 4.85/5.06  thf('140', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((m1_subset_1 @ (u1_struct_0 @ (sk_C @ (u1_struct_0 @ X0) @ X0)) @ 
% 4.85/5.06           (k9_setfam_1 @ (u1_struct_0 @ X0)))
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 4.85/5.06      inference('simplify', [status(thm)], ['139'])).
% 4.85/5.06  thf('141', plain,
% 4.85/5.06      (![X24 : $i, X25 : $i]:
% 4.85/5.06         (~ (v2_pre_topc @ X25)
% 4.85/5.06          | ~ (l1_pre_topc @ X25)
% 4.85/5.06          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 4.85/5.06               (k9_setfam_1 @ (u1_struct_0 @ X25)))
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ X24) @ X25)
% 4.85/5.06          | ~ (v1_borsuk_1 @ X24 @ X25)
% 4.85/5.06          | ~ (m1_pre_topc @ X24 @ X25))),
% 4.85/5.06      inference('demod', [status(thm)], ['25', '26'])).
% 4.85/5.06  thf('142', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (m1_pre_topc @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | ~ (v1_borsuk_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ (u1_struct_0 @ X0) @ X0)) @ 
% 4.85/5.06             X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0))),
% 4.85/5.06      inference('sup-', [status(thm)], ['140', '141'])).
% 4.85/5.06  thf('143', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         (~ (v2_pre_topc @ X0)
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ (u1_struct_0 @ X0) @ X0)) @ 
% 4.85/5.06             X0)
% 4.85/5.06          | ~ (v1_borsuk_1 @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | ~ (m1_pre_topc @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 4.85/5.06      inference('simplify', [status(thm)], ['142'])).
% 4.85/5.06  thf('144', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (m1_pre_topc @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ (u1_struct_0 @ X0) @ X0)) @ 
% 4.85/5.06             X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0))),
% 4.85/5.06      inference('sup-', [status(thm)], ['134', '143'])).
% 4.85/5.06  thf('145', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v4_pre_topc @ (u1_struct_0 @ (sk_C @ (u1_struct_0 @ X0) @ X0)) @ X0)
% 4.85/5.06          | ~ (m1_pre_topc @ (sk_C @ (u1_struct_0 @ X0) @ X0) @ X0)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 4.85/5.06      inference('simplify', [status(thm)], ['144'])).
% 4.85/5.06  thf('146', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X0)
% 4.85/5.06          | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ (u1_struct_0 @ X0) @ X0)) @ 
% 4.85/5.06             X0))),
% 4.85/5.06      inference('sup-', [status(thm)], ['130', '145'])).
% 4.85/5.06  thf('147', plain,
% 4.85/5.06      (![X0 : $i]:
% 4.85/5.06         ((v4_pre_topc @ (u1_struct_0 @ (sk_C @ (u1_struct_0 @ X0) @ X0)) @ X0)
% 4.85/5.06          | ~ (v1_tdlat_3 @ X0)
% 4.85/5.06          | ~ (v2_pre_topc @ X0)
% 4.85/5.06          | (v2_struct_0 @ X0)
% 4.85/5.06          | ~ (l1_pre_topc @ X0)
% 4.85/5.06          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 4.85/5.06      inference('simplify', [status(thm)], ['146'])).
% 4.85/5.06  thf('148', plain,
% 4.85/5.06      ((((v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 4.85/5.06         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 4.85/5.06         | ~ (l1_pre_topc @ sk_A)
% 4.85/5.06         | (v2_struct_0 @ sk_A)
% 4.85/5.06         | ~ (v2_pre_topc @ sk_A)
% 4.85/5.06         | ~ (v1_tdlat_3 @ sk_A)))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('sup+', [status(thm)], ['127', '147'])).
% 4.85/5.06  thf('149', plain,
% 4.85/5.06      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('sup-', [status(thm)], ['125', '126'])).
% 4.85/5.06  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('151', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('152', plain, ((v1_tdlat_3 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('153', plain,
% 4.85/5.06      ((((v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 4.85/5.06         | (v1_xboole_0 @ sk_B_2)
% 4.85/5.06         | (v2_struct_0 @ sk_A)))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('demod', [status(thm)], ['148', '149', '150', '151', '152'])).
% 4.85/5.06  thf('154', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('155', plain,
% 4.85/5.06      ((((v1_xboole_0 @ sk_B_2)
% 4.85/5.06         | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('clc', [status(thm)], ['153', '154'])).
% 4.85/5.06  thf('156', plain,
% 4.85/5.06      ((((v4_pre_topc @ sk_B_2 @ sk_A)
% 4.85/5.06         | (v1_xboole_0 @ sk_B_2)
% 4.85/5.06         | (v1_xboole_0 @ sk_B_2)))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('sup+', [status(thm)], ['120', '155'])).
% 4.85/5.06  thf('157', plain,
% 4.85/5.06      ((((v1_xboole_0 @ sk_B_2) | (v4_pre_topc @ sk_B_2 @ sk_A)))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('simplify', [status(thm)], ['156'])).
% 4.85/5.06  thf('158', plain,
% 4.85/5.06      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 4.85/5.06        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 4.85/5.06      inference('demod', [status(thm)], ['59', '60'])).
% 4.85/5.06  thf('159', plain,
% 4.85/5.06      ((((v1_xboole_0 @ sk_B_2) | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.06      inference('sup-', [status(thm)], ['157', '158'])).
% 4.85/5.06  thf('160', plain,
% 4.85/5.06      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.06  thf('161', plain,
% 4.85/5.06      (![X33 : $i, X34 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 4.85/5.06          | ((k2_pre_topc @ X34 @ X33) != (u1_struct_0 @ X34))
% 4.85/5.06          | (v1_tops_1 @ X33 @ X34)
% 4.85/5.06          | ~ (l1_pre_topc @ X34))),
% 4.85/5.06      inference('cnf', [status(esa)], [d2_tops_3])).
% 4.85/5.06  thf('162', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.06  thf('163', plain,
% 4.85/5.06      (![X33 : $i, X34 : $i]:
% 4.85/5.06         (~ (m1_subset_1 @ X33 @ (k9_setfam_1 @ (u1_struct_0 @ X34)))
% 4.85/5.06          | ((k2_pre_topc @ X34 @ X33) != (u1_struct_0 @ X34))
% 4.85/5.06          | (v1_tops_1 @ X33 @ X34)
% 4.85/5.06          | ~ (l1_pre_topc @ X34))),
% 4.85/5.06      inference('demod', [status(thm)], ['161', '162'])).
% 4.85/5.06  thf('164', plain,
% 4.85/5.06      ((~ (l1_pre_topc @ sk_A)
% 4.85/5.06        | (v1_tops_1 @ sk_B_2 @ sk_A)
% 4.85/5.06        | ((k2_pre_topc @ sk_A @ sk_B_2) != (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('sup-', [status(thm)], ['160', '163'])).
% 4.85/5.06  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.06  thf('166', plain,
% 4.85/5.06      (((v1_tops_1 @ sk_B_2 @ sk_A)
% 4.85/5.06        | ((k2_pre_topc @ sk_A @ sk_B_2) != (u1_struct_0 @ sk_A)))),
% 4.85/5.06      inference('demod', [status(thm)], ['164', '165'])).
% 4.85/5.06  thf('167', plain,
% 4.85/5.06      (((((sk_B_2) != (u1_struct_0 @ sk_A))
% 4.85/5.06         | (v1_xboole_0 @ sk_B_2)
% 4.85/5.06         | (v1_tops_1 @ sk_B_2 @ sk_A)))
% 4.85/5.06         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['159', '166'])).
% 4.85/5.07  thf('168', plain,
% 4.85/5.07      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['125', '126'])).
% 4.85/5.07  thf('169', plain,
% 4.85/5.07      (((((sk_B_2) != (sk_B_2))
% 4.85/5.07         | (v1_xboole_0 @ sk_B_2)
% 4.85/5.07         | (v1_tops_1 @ sk_B_2 @ sk_A)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('demod', [status(thm)], ['167', '168'])).
% 4.85/5.07  thf('170', plain,
% 4.85/5.07      ((((v1_tops_1 @ sk_B_2 @ sk_A) | (v1_xboole_0 @ sk_B_2)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('simplify', [status(thm)], ['169'])).
% 4.85/5.07  thf('171', plain,
% 4.85/5.07      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.07      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.07  thf(t48_tex_2, axiom,
% 4.85/5.07    (![A:$i]:
% 4.85/5.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.85/5.07       ( ![B:$i]:
% 4.85/5.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.85/5.07           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 4.85/5.07             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 4.85/5.07  thf('172', plain,
% 4.85/5.07      (![X49 : $i, X50 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 4.85/5.07          | (v3_tex_2 @ X49 @ X50)
% 4.85/5.07          | ~ (v2_tex_2 @ X49 @ X50)
% 4.85/5.07          | ~ (v1_tops_1 @ X49 @ X50)
% 4.85/5.07          | ~ (l1_pre_topc @ X50)
% 4.85/5.07          | ~ (v2_pre_topc @ X50)
% 4.85/5.07          | (v2_struct_0 @ X50))),
% 4.85/5.07      inference('cnf', [status(esa)], [t48_tex_2])).
% 4.85/5.07  thf('173', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.07      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.07  thf('174', plain,
% 4.85/5.07      (![X49 : $i, X50 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X49 @ (k9_setfam_1 @ (u1_struct_0 @ X50)))
% 4.85/5.07          | (v3_tex_2 @ X49 @ X50)
% 4.85/5.07          | ~ (v2_tex_2 @ X49 @ X50)
% 4.85/5.07          | ~ (v1_tops_1 @ X49 @ X50)
% 4.85/5.07          | ~ (l1_pre_topc @ X50)
% 4.85/5.07          | ~ (v2_pre_topc @ X50)
% 4.85/5.07          | (v2_struct_0 @ X50))),
% 4.85/5.07      inference('demod', [status(thm)], ['172', '173'])).
% 4.85/5.07  thf('175', plain,
% 4.85/5.07      (((v2_struct_0 @ sk_A)
% 4.85/5.07        | ~ (v2_pre_topc @ sk_A)
% 4.85/5.07        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.07        | ~ (v1_tops_1 @ sk_B_2 @ sk_A)
% 4.85/5.07        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 4.85/5.07        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.07      inference('sup-', [status(thm)], ['171', '174'])).
% 4.85/5.07  thf('176', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('178', plain,
% 4.85/5.07      ((m1_subset_1 @ sk_B_2 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 4.85/5.07      inference('demod', [status(thm)], ['2', '3'])).
% 4.85/5.07  thf(t43_tex_2, axiom,
% 4.85/5.07    (![A:$i]:
% 4.85/5.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 4.85/5.07         ( l1_pre_topc @ A ) ) =>
% 4.85/5.07       ( ![B:$i]:
% 4.85/5.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.85/5.07           ( v2_tex_2 @ B @ A ) ) ) ))).
% 4.85/5.07  thf('179', plain,
% 4.85/5.07      (![X43 : $i, X44 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 4.85/5.07          | (v2_tex_2 @ X43 @ X44)
% 4.85/5.07          | ~ (l1_pre_topc @ X44)
% 4.85/5.07          | ~ (v1_tdlat_3 @ X44)
% 4.85/5.07          | ~ (v2_pre_topc @ X44)
% 4.85/5.07          | (v2_struct_0 @ X44))),
% 4.85/5.07      inference('cnf', [status(esa)], [t43_tex_2])).
% 4.85/5.07  thf('180', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.07      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.07  thf('181', plain,
% 4.85/5.07      (![X43 : $i, X44 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X43 @ (k9_setfam_1 @ (u1_struct_0 @ X44)))
% 4.85/5.07          | (v2_tex_2 @ X43 @ X44)
% 4.85/5.07          | ~ (l1_pre_topc @ X44)
% 4.85/5.07          | ~ (v1_tdlat_3 @ X44)
% 4.85/5.07          | ~ (v2_pre_topc @ X44)
% 4.85/5.07          | (v2_struct_0 @ X44))),
% 4.85/5.07      inference('demod', [status(thm)], ['179', '180'])).
% 4.85/5.07  thf('182', plain,
% 4.85/5.07      (((v2_struct_0 @ sk_A)
% 4.85/5.07        | ~ (v2_pre_topc @ sk_A)
% 4.85/5.07        | ~ (v1_tdlat_3 @ sk_A)
% 4.85/5.07        | ~ (l1_pre_topc @ sk_A)
% 4.85/5.07        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.07      inference('sup-', [status(thm)], ['178', '181'])).
% 4.85/5.07  thf('183', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('184', plain, ((v1_tdlat_3 @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('186', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.07      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 4.85/5.07  thf('187', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('188', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 4.85/5.07      inference('clc', [status(thm)], ['186', '187'])).
% 4.85/5.07  thf('189', plain,
% 4.85/5.07      (((v2_struct_0 @ sk_A)
% 4.85/5.07        | ~ (v1_tops_1 @ sk_B_2 @ sk_A)
% 4.85/5.07        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.07      inference('demod', [status(thm)], ['175', '176', '177', '188'])).
% 4.85/5.07  thf('190', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('191', plain,
% 4.85/5.07      (((v3_tex_2 @ sk_B_2 @ sk_A) | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 4.85/5.07      inference('clc', [status(thm)], ['189', '190'])).
% 4.85/5.07  thf('192', plain,
% 4.85/5.07      ((((v1_xboole_0 @ sk_B_2) | (v3_tex_2 @ sk_B_2 @ sk_A)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['170', '191'])).
% 4.85/5.07  thf('193', plain,
% 4.85/5.07      ((~ (v3_tex_2 @ sk_B_2 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.07      inference('split', [status(esa)], ['0'])).
% 4.85/5.07  thf('194', plain,
% 4.85/5.07      (((v1_xboole_0 @ sk_B_2))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 4.85/5.07             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.07      inference('sup-', [status(thm)], ['192', '193'])).
% 4.85/5.07  thf(dt_k1_subset_1, axiom,
% 4.85/5.07    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 4.85/5.07  thf('195', plain,
% 4.85/5.07      (![X5 : $i]: (m1_subset_1 @ (k1_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 4.85/5.07      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 4.85/5.07  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 4.85/5.07  thf('196', plain, (![X3 : $i]: ((k1_subset_1 @ X3) = (k1_xboole_0))),
% 4.85/5.07      inference('cnf', [status(esa)], [d3_subset_1])).
% 4.85/5.07  thf('197', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.07      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.07  thf('198', plain,
% 4.85/5.07      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X5))),
% 4.85/5.07      inference('demod', [status(thm)], ['195', '196', '197'])).
% 4.85/5.07  thf('199', plain,
% 4.85/5.07      (![X35 : $i, X36 : $i]:
% 4.85/5.07         (((X36) = (X35))
% 4.85/5.07          | (v1_subset_1 @ X36 @ X35)
% 4.85/5.07          | ~ (m1_subset_1 @ X36 @ (k9_setfam_1 @ X35)))),
% 4.85/5.07      inference('demod', [status(thm)], ['122', '123'])).
% 4.85/5.07  thf('200', plain,
% 4.85/5.07      (![X0 : $i]: ((v1_subset_1 @ k1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 4.85/5.07      inference('sup-', [status(thm)], ['198', '199'])).
% 4.85/5.07  thf('201', plain,
% 4.85/5.07      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X5))),
% 4.85/5.07      inference('demod', [status(thm)], ['195', '196', '197'])).
% 4.85/5.07  thf(cc4_subset_1, axiom,
% 4.85/5.07    (![A:$i]:
% 4.85/5.07     ( ( v1_xboole_0 @ A ) =>
% 4.85/5.07       ( ![B:$i]:
% 4.85/5.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.85/5.07           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 4.85/5.07  thf('202', plain,
% 4.85/5.07      (![X12 : $i, X13 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 4.85/5.07          | ~ (v1_subset_1 @ X12 @ X13)
% 4.85/5.07          | ~ (v1_xboole_0 @ X13))),
% 4.85/5.07      inference('cnf', [status(esa)], [cc4_subset_1])).
% 4.85/5.07  thf('203', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.07      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.07  thf('204', plain,
% 4.85/5.07      (![X12 : $i, X13 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X12 @ (k9_setfam_1 @ X13))
% 4.85/5.07          | ~ (v1_subset_1 @ X12 @ X13)
% 4.85/5.07          | ~ (v1_xboole_0 @ X13))),
% 4.85/5.07      inference('demod', [status(thm)], ['202', '203'])).
% 4.85/5.07  thf('205', plain,
% 4.85/5.07      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_subset_1 @ k1_xboole_0 @ X0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['201', '204'])).
% 4.85/5.07  thf('206', plain,
% 4.85/5.07      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['200', '205'])).
% 4.85/5.07  thf('207', plain,
% 4.85/5.07      ((((k1_xboole_0) = (sk_B_2)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 4.85/5.07             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.07      inference('sup-', [status(thm)], ['194', '206'])).
% 4.85/5.07  thf('208', plain,
% 4.85/5.07      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['125', '126'])).
% 4.85/5.07  thf(rc3_tops_1, axiom,
% 4.85/5.07    (![A:$i]:
% 4.85/5.07     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.85/5.07       ( ?[B:$i]:
% 4.85/5.07         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 4.85/5.07           ( ~( v1_xboole_0 @ B ) ) & 
% 4.85/5.07           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.85/5.07  thf('209', plain,
% 4.85/5.07      (![X23 : $i]:
% 4.85/5.07         ((m1_subset_1 @ (sk_B @ X23) @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 4.85/5.07          | ~ (l1_pre_topc @ X23)
% 4.85/5.07          | ~ (v2_pre_topc @ X23)
% 4.85/5.07          | (v2_struct_0 @ X23))),
% 4.85/5.07      inference('cnf', [status(esa)], [rc3_tops_1])).
% 4.85/5.07  thf('210', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.07      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.07  thf('211', plain,
% 4.85/5.07      (![X23 : $i]:
% 4.85/5.07         ((m1_subset_1 @ (sk_B @ X23) @ (k9_setfam_1 @ (u1_struct_0 @ X23)))
% 4.85/5.07          | ~ (l1_pre_topc @ X23)
% 4.85/5.07          | ~ (v2_pre_topc @ X23)
% 4.85/5.07          | (v2_struct_0 @ X23))),
% 4.85/5.07      inference('demod', [status(thm)], ['209', '210'])).
% 4.85/5.07  thf('212', plain,
% 4.85/5.07      ((((m1_subset_1 @ (sk_B @ sk_A) @ (k9_setfam_1 @ sk_B_2))
% 4.85/5.07         | (v2_struct_0 @ sk_A)
% 4.85/5.07         | ~ (v2_pre_topc @ sk_A)
% 4.85/5.07         | ~ (l1_pre_topc @ sk_A)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('sup+', [status(thm)], ['208', '211'])).
% 4.85/5.07  thf('213', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('214', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('215', plain,
% 4.85/5.07      ((((m1_subset_1 @ (sk_B @ sk_A) @ (k9_setfam_1 @ sk_B_2))
% 4.85/5.07         | (v2_struct_0 @ sk_A)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('demod', [status(thm)], ['212', '213', '214'])).
% 4.85/5.07  thf('216', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('217', plain,
% 4.85/5.07      (((m1_subset_1 @ (sk_B @ sk_A) @ (k9_setfam_1 @ sk_B_2)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('clc', [status(thm)], ['215', '216'])).
% 4.85/5.07  thf('218', plain,
% 4.85/5.07      (![X35 : $i, X36 : $i]:
% 4.85/5.07         (((X36) = (X35))
% 4.85/5.07          | (v1_subset_1 @ X36 @ X35)
% 4.85/5.07          | ~ (m1_subset_1 @ X36 @ (k9_setfam_1 @ X35)))),
% 4.85/5.07      inference('demod', [status(thm)], ['122', '123'])).
% 4.85/5.07  thf('219', plain,
% 4.85/5.07      ((((v1_subset_1 @ (sk_B @ sk_A) @ sk_B_2) | ((sk_B @ sk_A) = (sk_B_2))))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['217', '218'])).
% 4.85/5.07  thf('220', plain,
% 4.85/5.07      (((m1_subset_1 @ (sk_B @ sk_A) @ (k9_setfam_1 @ sk_B_2)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('clc', [status(thm)], ['215', '216'])).
% 4.85/5.07  thf('221', plain,
% 4.85/5.07      (![X12 : $i, X13 : $i]:
% 4.85/5.07         (~ (m1_subset_1 @ X12 @ (k9_setfam_1 @ X13))
% 4.85/5.07          | ~ (v1_subset_1 @ X12 @ X13)
% 4.85/5.07          | ~ (v1_xboole_0 @ X13))),
% 4.85/5.07      inference('demod', [status(thm)], ['202', '203'])).
% 4.85/5.07  thf('222', plain,
% 4.85/5.07      (((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_subset_1 @ (sk_B @ sk_A) @ sk_B_2)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['220', '221'])).
% 4.85/5.07  thf('223', plain,
% 4.85/5.07      (((((sk_B @ sk_A) = (sk_B_2)) | ~ (v1_xboole_0 @ sk_B_2)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 4.85/5.07      inference('sup-', [status(thm)], ['219', '222'])).
% 4.85/5.07  thf('224', plain,
% 4.85/5.07      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B @ sk_A) = (sk_B_2))))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 4.85/5.07             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.07      inference('sup-', [status(thm)], ['207', '223'])).
% 4.85/5.07  thf('225', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k9_setfam_1 @ X6))),
% 4.85/5.07      inference('demod', [status(thm)], ['113', '114', '115'])).
% 4.85/5.07  thf(t3_subset, axiom,
% 4.85/5.07    (![A:$i,B:$i]:
% 4.85/5.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.85/5.07  thf('226', plain,
% 4.85/5.07      (![X14 : $i, X15 : $i]:
% 4.85/5.07         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 4.85/5.07      inference('cnf', [status(esa)], [t3_subset])).
% 4.85/5.07  thf('227', plain, (![X17 : $i]: ((k9_setfam_1 @ X17) = (k1_zfmisc_1 @ X17))),
% 4.85/5.07      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 4.85/5.07  thf('228', plain,
% 4.85/5.07      (![X14 : $i, X15 : $i]:
% 4.85/5.07         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k9_setfam_1 @ X15)))),
% 4.85/5.07      inference('demod', [status(thm)], ['226', '227'])).
% 4.85/5.07  thf('229', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 4.85/5.07      inference('sup-', [status(thm)], ['225', '228'])).
% 4.85/5.07  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 4.85/5.07  thf('230', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.85/5.07      inference('cnf', [status(esa)], [t65_xboole_1])).
% 4.85/5.07  thf(t69_xboole_1, axiom,
% 4.85/5.07    (![A:$i,B:$i]:
% 4.85/5.07     ( ( ~( v1_xboole_0 @ B ) ) =>
% 4.85/5.07       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 4.85/5.07  thf('231', plain,
% 4.85/5.07      (![X1 : $i, X2 : $i]:
% 4.85/5.07         (~ (r1_xboole_0 @ X1 @ X2)
% 4.85/5.07          | ~ (r1_tarski @ X1 @ X2)
% 4.85/5.07          | (v1_xboole_0 @ X1))),
% 4.85/5.07      inference('cnf', [status(esa)], [t69_xboole_1])).
% 4.85/5.07  thf('232', plain,
% 4.85/5.07      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 4.85/5.07      inference('sup-', [status(thm)], ['230', '231'])).
% 4.85/5.07  thf('233', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.85/5.07      inference('sup-', [status(thm)], ['229', '232'])).
% 4.85/5.07  thf('234', plain,
% 4.85/5.07      ((((k1_xboole_0) = (sk_B_2)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 4.85/5.07             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.07      inference('sup-', [status(thm)], ['194', '206'])).
% 4.85/5.07  thf('235', plain,
% 4.85/5.07      ((((sk_B @ sk_A) = (k1_xboole_0)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 4.85/5.07             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.07      inference('demod', [status(thm)], ['224', '233', '234'])).
% 4.85/5.07  thf('236', plain,
% 4.85/5.07      (![X23 : $i]:
% 4.85/5.07         (~ (v1_xboole_0 @ (sk_B @ X23))
% 4.85/5.07          | ~ (l1_pre_topc @ X23)
% 4.85/5.07          | ~ (v2_pre_topc @ X23)
% 4.85/5.07          | (v2_struct_0 @ X23))),
% 4.85/5.07      inference('cnf', [status(esa)], [rc3_tops_1])).
% 4.85/5.07  thf('237', plain,
% 4.85/5.07      (((~ (v1_xboole_0 @ k1_xboole_0)
% 4.85/5.07         | (v2_struct_0 @ sk_A)
% 4.85/5.07         | ~ (v2_pre_topc @ sk_A)
% 4.85/5.07         | ~ (l1_pre_topc @ sk_A)))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 4.85/5.07             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.07      inference('sup-', [status(thm)], ['235', '236'])).
% 4.85/5.07  thf('238', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.85/5.07      inference('sup-', [status(thm)], ['229', '232'])).
% 4.85/5.07  thf('239', plain, ((v2_pre_topc @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('240', plain, ((l1_pre_topc @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('241', plain,
% 4.85/5.07      (((v2_struct_0 @ sk_A))
% 4.85/5.07         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 4.85/5.07             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 4.85/5.07      inference('demod', [status(thm)], ['237', '238', '239', '240'])).
% 4.85/5.07  thf('242', plain, (~ (v2_struct_0 @ sk_A)),
% 4.85/5.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.85/5.07  thf('243', plain,
% 4.85/5.07      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 4.85/5.07       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 4.85/5.07      inference('sup-', [status(thm)], ['241', '242'])).
% 4.85/5.07  thf('244', plain, ($false),
% 4.85/5.07      inference('sat_resolution*', [status(thm)], ['1', '118', '119', '243'])).
% 4.85/5.07  
% 4.85/5.07  % SZS output end Refutation
% 4.85/5.07  
% 4.85/5.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
