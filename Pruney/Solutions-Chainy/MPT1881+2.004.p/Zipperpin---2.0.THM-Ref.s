%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oz8uUjwvCs

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:12 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 739 expanded)
%              Number of leaves         :   50 ( 225 expanded)
%              Depth                    :   26
%              Number of atoms          : 1825 (9022 expanded)
%              Number of equality atoms :   50 ( 135 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( X34
        = ( u1_struct_0 @ ( sk_C @ X34 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X34 @ X35 ) @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( X22
       != ( u1_struct_0 @ X20 ) )
      | ~ ( v1_borsuk_1 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v4_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X20 ) @ X21 )
      | ~ ( v1_borsuk_1 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,
    ( ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

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

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v1_borsuk_1 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v1_tdlat_3 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['28','37'])).

thf('39',plain,
    ( ( v4_pre_topc @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['8','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('50',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( v1_tops_1 @ X42 @ X43 )
      | ~ ( v3_tex_2 @ X42 @ X43 )
      | ~ ( v3_pre_topc @ X42 @ X43 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('55',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_tdlat_3 @ X36 )
      | ( v3_pre_topc @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t17_tdlat_3])).

thf('56',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_2 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_pre_topc @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v1_tops_1 @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ( ( sk_B_2
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['46','70'])).

thf('72',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['47'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('74',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ~ ( v3_tex_2 @ X40 @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['71','81'])).

thf('83',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( v1_subset_1 @ sk_B_2 @ sk_B_2 )
   <= ( ( v3_tex_2 @ sk_B_2 @ sk_A )
      & ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('85',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_subset_1 @ X31 @ X30 )
      | ( X31 != X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('86',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( v1_subset_1 @ X30 @ X30 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('87',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('88',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('89',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X30: $i] :
      ~ ( v1_subset_1 @ X30 @ X30 ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','90'])).

thf('92',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['47'])).

thf('93',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('94',plain,
    ( ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('95',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ( v1_subset_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('98',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_2
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('100',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X20 ) @ X21 )
      | ~ ( v1_borsuk_1 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_borsuk_1 @ X0 @ sk_A )
        | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A )
        | ~ ( v1_borsuk_1 @ X0 @ sk_A )
        | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ~ ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
      | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','105'])).

thf('107',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('108',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
      | ~ ( v1_borsuk_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','108'])).

thf('110',plain,
    ( ( ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('112',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v4_pre_topc @ ( u1_struct_0 @ ( sk_C @ sk_B_2 @ sk_A ) ) @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( v4_pre_topc @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['93','112'])).

thf('114',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v4_pre_topc @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_2 )
      = sk_B_2 )
    | ~ ( v4_pre_topc @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('116',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
        = sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_pre_topc @ X29 @ X28 )
       != ( u1_struct_0 @ X29 ) )
      | ( v1_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_2 )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( sk_B_2
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_tops_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('124',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( v1_tops_1 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( v1_tops_1 @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('127',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( v3_tex_2 @ X44 @ X45 )
      | ~ ( v2_tex_2 @ X44 @ X45 )
      | ~ ( v1_tops_1 @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t48_tex_2])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('132',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( v2_tex_2 @ X38 @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_tdlat_3 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129','130','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v3_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_tops_1 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v3_tex_2 @ sk_B_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['125','142'])).

thf('144',plain,
    ( ~ ( v3_tex_2 @ sk_B_2 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('146',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('147',plain,(
    ! [X3: $i] :
      ( ( k1_subset_1 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('148',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ( v1_subset_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('152',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( v1_subset_1 @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,
    ( ( k1_xboole_0 = sk_B_2 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','154'])).

thf('156',plain,
    ( ( sk_B_2
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

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

thf('157',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('158',plain,
    ( ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ( v1_subset_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('165',plain,
    ( ( ( v1_subset_1 @ ( sk_B @ sk_A ) @ sk_B_2 )
      | ( ( sk_B @ sk_A )
        = sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('167',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( v1_subset_1 @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('168',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_subset_1 @ ( sk_B @ sk_A ) @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( ( sk_B @ sk_A )
        = sk_B_2 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('170',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = sk_B_2 ) )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','169'])).

thf('171',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('172',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('173',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('174',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('175',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,
    ( ( k1_xboole_0 = sk_B_2 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','154'])).

thf('179',plain,
    ( ( ( sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','177','178'])).

thf('180',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('181',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['173','176'])).

thf('183',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
      & ~ ( v3_tex_2 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','91','92','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oz8uUjwvCs
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.26/2.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.26/2.48  % Solved by: fo/fo7.sh
% 2.26/2.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.26/2.48  % done 2327 iterations in 2.027s
% 2.26/2.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.26/2.48  % SZS output start Refutation
% 2.26/2.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 2.26/2.48  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 2.26/2.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.26/2.48  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 2.26/2.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.26/2.48  thf(sk_B_type, type, sk_B: $i > $i).
% 2.26/2.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.26/2.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.26/2.48  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.26/2.48  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 2.26/2.48  thf(sk_A_type, type, sk_A: $i).
% 2.26/2.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.26/2.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.26/2.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.26/2.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 2.26/2.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.26/2.48  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 2.26/2.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.26/2.48  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 2.26/2.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.26/2.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 2.26/2.48  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 2.26/2.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.26/2.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.26/2.48  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 2.26/2.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.26/2.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.26/2.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.26/2.48  thf(t49_tex_2, conjecture,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 2.26/2.48         ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.48           ( ( v3_tex_2 @ B @ A ) <=>
% 2.26/2.48             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 2.26/2.48  thf(zf_stmt_0, negated_conjecture,
% 2.26/2.48    (~( ![A:$i]:
% 2.26/2.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.26/2.48            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.48          ( ![B:$i]:
% 2.26/2.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.48              ( ( v3_tex_2 @ B @ A ) <=>
% 2.26/2.48                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 2.26/2.48    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 2.26/2.48  thf('0', plain,
% 2.26/2.48      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 2.26/2.48        | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('1', plain,
% 2.26/2.48      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 2.26/2.48       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('split', [status(esa)], ['0'])).
% 2.26/2.48  thf('2', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf(t10_tsep_1, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 2.26/2.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.26/2.48           ( ?[C:$i]:
% 2.26/2.48             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 2.26/2.48               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 2.26/2.48  thf('3', plain,
% 2.26/2.48      (![X34 : $i, X35 : $i]:
% 2.26/2.48         ((v1_xboole_0 @ X34)
% 2.26/2.48          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.26/2.48          | ((X34) = (u1_struct_0 @ (sk_C @ X34 @ X35)))
% 2.26/2.48          | ~ (l1_pre_topc @ X35)
% 2.26/2.48          | (v2_struct_0 @ X35))),
% 2.26/2.48      inference('cnf', [status(esa)], [t10_tsep_1])).
% 2.26/2.48  thf('4', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)))
% 2.26/2.48        | (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('sup-', [status(thm)], ['2', '3'])).
% 2.26/2.48  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('6', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)))
% 2.26/2.48        | (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('demod', [status(thm)], ['4', '5'])).
% 2.26/2.48  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('8', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A))))),
% 2.26/2.48      inference('clc', [status(thm)], ['6', '7'])).
% 2.26/2.48  thf('9', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('10', plain,
% 2.26/2.48      (![X34 : $i, X35 : $i]:
% 2.26/2.48         ((v1_xboole_0 @ X34)
% 2.26/2.48          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.26/2.48          | (m1_pre_topc @ (sk_C @ X34 @ X35) @ X35)
% 2.26/2.48          | ~ (l1_pre_topc @ X35)
% 2.26/2.48          | (v2_struct_0 @ X35))),
% 2.26/2.48      inference('cnf', [status(esa)], [t10_tsep_1])).
% 2.26/2.48  thf('11', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48        | (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('sup-', [status(thm)], ['9', '10'])).
% 2.26/2.48  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('13', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48        | (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('demod', [status(thm)], ['11', '12'])).
% 2.26/2.48  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('15', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2) | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 2.26/2.48      inference('clc', [status(thm)], ['13', '14'])).
% 2.26/2.48  thf('16', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2) | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 2.26/2.48      inference('clc', [status(thm)], ['13', '14'])).
% 2.26/2.48  thf(t1_tsep_1, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( l1_pre_topc @ A ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_pre_topc @ B @ A ) =>
% 2.26/2.48           ( m1_subset_1 @
% 2.26/2.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.26/2.48  thf('17', plain,
% 2.26/2.48      (![X23 : $i, X24 : $i]:
% 2.26/2.48         (~ (m1_pre_topc @ X23 @ X24)
% 2.26/2.48          | (m1_subset_1 @ (u1_struct_0 @ X23) @ 
% 2.26/2.48             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 2.26/2.48          | ~ (l1_pre_topc @ X24))),
% 2.26/2.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 2.26/2.48  thf('18', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | (m1_subset_1 @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ 
% 2.26/2.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['16', '17'])).
% 2.26/2.48  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('20', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | (m1_subset_1 @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ 
% 2.26/2.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('demod', [status(thm)], ['18', '19'])).
% 2.26/2.48  thf(t11_tsep_1, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_pre_topc @ B @ A ) =>
% 2.26/2.48           ( ![C:$i]:
% 2.26/2.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.48               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 2.26/2.48                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 2.26/2.48                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 2.26/2.48  thf('21', plain,
% 2.26/2.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.26/2.48         (~ (m1_pre_topc @ X20 @ X21)
% 2.26/2.48          | ((X22) != (u1_struct_0 @ X20))
% 2.26/2.48          | ~ (v1_borsuk_1 @ X20 @ X21)
% 2.26/2.48          | ~ (m1_pre_topc @ X20 @ X21)
% 2.26/2.48          | (v4_pre_topc @ X22 @ X21)
% 2.26/2.48          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.26/2.48          | ~ (l1_pre_topc @ X21)
% 2.26/2.48          | ~ (v2_pre_topc @ X21))),
% 2.26/2.48      inference('cnf', [status(esa)], [t11_tsep_1])).
% 2.26/2.48  thf('22', plain,
% 2.26/2.48      (![X20 : $i, X21 : $i]:
% 2.26/2.48         (~ (v2_pre_topc @ X21)
% 2.26/2.48          | ~ (l1_pre_topc @ X21)
% 2.26/2.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 2.26/2.48               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.26/2.48          | (v4_pre_topc @ (u1_struct_0 @ X20) @ X21)
% 2.26/2.48          | ~ (v1_borsuk_1 @ X20 @ X21)
% 2.26/2.48          | ~ (m1_pre_topc @ X20 @ X21))),
% 2.26/2.48      inference('simplify', [status(thm)], ['21'])).
% 2.26/2.48  thf('23', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | ~ (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48        | ~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | ~ (v2_pre_topc @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['20', '22'])).
% 2.26/2.48  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('26', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | ~ (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48        | ~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A))),
% 2.26/2.48      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.26/2.48  thf('27', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 2.26/2.48        | ~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48        | (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('sup-', [status(thm)], ['15', '26'])).
% 2.26/2.48  thf('28', plain,
% 2.26/2.48      ((~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 2.26/2.48        | (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('simplify', [status(thm)], ['27'])).
% 2.26/2.48  thf('29', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2) | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 2.26/2.48      inference('clc', [status(thm)], ['13', '14'])).
% 2.26/2.48  thf(cc5_tdlat_3, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 2.26/2.48         ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_pre_topc @ B @ A ) =>
% 2.26/2.48           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 2.26/2.48             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 2.26/2.48  thf('30', plain,
% 2.26/2.48      (![X26 : $i, X27 : $i]:
% 2.26/2.48         (~ (m1_pre_topc @ X26 @ X27)
% 2.26/2.48          | (v1_borsuk_1 @ X26 @ X27)
% 2.26/2.48          | ~ (l1_pre_topc @ X27)
% 2.26/2.48          | ~ (v1_tdlat_3 @ X27)
% 2.26/2.48          | ~ (v2_pre_topc @ X27)
% 2.26/2.48          | (v2_struct_0 @ X27))),
% 2.26/2.48      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 2.26/2.48  thf('31', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | (v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.26/2.48        | ~ (v1_tdlat_3 @ sk_A)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['29', '30'])).
% 2.26/2.48  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('33', plain, ((v1_tdlat_3 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('35', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | (v2_struct_0 @ sk_A)
% 2.26/2.48        | (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 2.26/2.48      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 2.26/2.48  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('37', plain,
% 2.26/2.48      (((v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A) | (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('clc', [status(thm)], ['35', '36'])).
% 2.26/2.48  thf('38', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A))),
% 2.26/2.48      inference('clc', [status(thm)], ['28', '37'])).
% 2.26/2.48  thf('39', plain,
% 2.26/2.48      (((v4_pre_topc @ sk_B_2 @ sk_A)
% 2.26/2.48        | (v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('sup+', [status(thm)], ['8', '38'])).
% 2.26/2.48  thf('40', plain, (((v1_xboole_0 @ sk_B_2) | (v4_pre_topc @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('simplify', [status(thm)], ['39'])).
% 2.26/2.48  thf('41', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf(t52_pre_topc, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( l1_pre_topc @ A ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.48           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 2.26/2.48             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 2.26/2.48               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 2.26/2.48  thf('42', plain,
% 2.26/2.48      (![X17 : $i, X18 : $i]:
% 2.26/2.48         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.26/2.48          | ~ (v4_pre_topc @ X17 @ X18)
% 2.26/2.48          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 2.26/2.48          | ~ (l1_pre_topc @ X18))),
% 2.26/2.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 2.26/2.48  thf('43', plain,
% 2.26/2.48      ((~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 2.26/2.48        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['41', '42'])).
% 2.26/2.48  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('45', plain,
% 2.26/2.48      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 2.26/2.48        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('demod', [status(thm)], ['43', '44'])).
% 2.26/2.48  thf('46', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2) | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['40', '45'])).
% 2.26/2.48  thf('47', plain,
% 2.26/2.48      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 2.26/2.48        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('48', plain,
% 2.26/2.48      (((v3_tex_2 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('split', [status(esa)], ['47'])).
% 2.26/2.48  thf('49', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf(t47_tex_2, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.48           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 2.26/2.48             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 2.26/2.48  thf('50', plain,
% 2.26/2.48      (![X42 : $i, X43 : $i]:
% 2.26/2.48         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 2.26/2.48          | (v1_tops_1 @ X42 @ X43)
% 2.26/2.48          | ~ (v3_tex_2 @ X42 @ X43)
% 2.26/2.48          | ~ (v3_pre_topc @ X42 @ X43)
% 2.26/2.48          | ~ (l1_pre_topc @ X43)
% 2.26/2.48          | ~ (v2_pre_topc @ X43)
% 2.26/2.48          | (v2_struct_0 @ X43))),
% 2.26/2.48      inference('cnf', [status(esa)], [t47_tex_2])).
% 2.26/2.48  thf('51', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | ~ (v3_pre_topc @ sk_B_2 @ sk_A)
% 2.26/2.48        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 2.26/2.48        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['49', '50'])).
% 2.26/2.48  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('54', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf(t17_tdlat_3, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ( v1_tdlat_3 @ A ) <=>
% 2.26/2.48         ( ![B:$i]:
% 2.26/2.48           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.48             ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 2.26/2.48  thf('55', plain,
% 2.26/2.48      (![X36 : $i, X37 : $i]:
% 2.26/2.48         (~ (v1_tdlat_3 @ X36)
% 2.26/2.48          | (v3_pre_topc @ X37 @ X36)
% 2.26/2.48          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 2.26/2.48          | ~ (l1_pre_topc @ X36)
% 2.26/2.48          | ~ (v2_pre_topc @ X36))),
% 2.26/2.48      inference('cnf', [status(esa)], [t17_tdlat_3])).
% 2.26/2.48  thf('56', plain,
% 2.26/2.48      ((~ (v2_pre_topc @ sk_A)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | (v3_pre_topc @ sk_B_2 @ sk_A)
% 2.26/2.48        | ~ (v1_tdlat_3 @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['54', '55'])).
% 2.26/2.48  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('59', plain, ((v1_tdlat_3 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('60', plain, ((v3_pre_topc @ sk_B_2 @ sk_A)),
% 2.26/2.48      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 2.26/2.48  thf('61', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 2.26/2.48        | (v1_tops_1 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('demod', [status(thm)], ['51', '52', '53', '60'])).
% 2.26/2.48  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('63', plain,
% 2.26/2.48      (((v1_tops_1 @ sk_B_2 @ sk_A) | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('clc', [status(thm)], ['61', '62'])).
% 2.26/2.48  thf('64', plain,
% 2.26/2.48      (((v1_tops_1 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['48', '63'])).
% 2.26/2.48  thf('65', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf(d2_tops_3, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( l1_pre_topc @ A ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.48           ( ( v1_tops_1 @ B @ A ) <=>
% 2.26/2.48             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.26/2.48  thf('66', plain,
% 2.26/2.48      (![X28 : $i, X29 : $i]:
% 2.26/2.48         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.26/2.48          | ~ (v1_tops_1 @ X28 @ X29)
% 2.26/2.48          | ((k2_pre_topc @ X29 @ X28) = (u1_struct_0 @ X29))
% 2.26/2.48          | ~ (l1_pre_topc @ X29))),
% 2.26/2.48      inference('cnf', [status(esa)], [d2_tops_3])).
% 2.26/2.48  thf('67', plain,
% 2.26/2.48      ((~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | ((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 2.26/2.48        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['65', '66'])).
% 2.26/2.48  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('69', plain,
% 2.26/2.48      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A))
% 2.26/2.48        | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('demod', [status(thm)], ['67', '68'])).
% 2.26/2.48  thf('70', plain,
% 2.26/2.48      ((((k2_pre_topc @ sk_A @ sk_B_2) = (u1_struct_0 @ sk_A)))
% 2.26/2.48         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['64', '69'])).
% 2.26/2.48  thf('71', plain,
% 2.26/2.48      (((((sk_B_2) = (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_2)))
% 2.26/2.48         <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('sup+', [status(thm)], ['46', '70'])).
% 2.26/2.48  thf('72', plain,
% 2.26/2.48      (((v3_tex_2 @ sk_B_2 @ sk_A)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('split', [status(esa)], ['47'])).
% 2.26/2.48  thf('73', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf(t46_tex_2, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( ( v1_xboole_0 @ B ) & 
% 2.26/2.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.26/2.48           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 2.26/2.48  thf('74', plain,
% 2.26/2.48      (![X40 : $i, X41 : $i]:
% 2.26/2.48         (~ (v1_xboole_0 @ X40)
% 2.26/2.48          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 2.26/2.48          | ~ (v3_tex_2 @ X40 @ X41)
% 2.26/2.48          | ~ (l1_pre_topc @ X41)
% 2.26/2.48          | ~ (v2_pre_topc @ X41)
% 2.26/2.48          | (v2_struct_0 @ X41))),
% 2.26/2.48      inference('cnf', [status(esa)], [t46_tex_2])).
% 2.26/2.48  thf('75', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 2.26/2.48        | ~ (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('sup-', [status(thm)], ['73', '74'])).
% 2.26/2.48  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('78', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (v3_tex_2 @ sk_B_2 @ sk_A)
% 2.26/2.48        | ~ (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.26/2.48  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('80', plain, ((~ (v1_xboole_0 @ sk_B_2) | ~ (v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('clc', [status(thm)], ['78', '79'])).
% 2.26/2.48  thf('81', plain,
% 2.26/2.48      ((~ (v1_xboole_0 @ sk_B_2)) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['72', '80'])).
% 2.26/2.48  thf('82', plain,
% 2.26/2.48      ((((sk_B_2) = (u1_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('clc', [status(thm)], ['71', '81'])).
% 2.26/2.48  thf('83', plain,
% 2.26/2.48      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 2.26/2.48         <= (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('split', [status(esa)], ['0'])).
% 2.26/2.48  thf('84', plain,
% 2.26/2.48      (((v1_subset_1 @ sk_B_2 @ sk_B_2))
% 2.26/2.48         <= (((v3_tex_2 @ sk_B_2 @ sk_A)) & 
% 2.26/2.48             ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup+', [status(thm)], ['82', '83'])).
% 2.26/2.48  thf(d7_subset_1, axiom,
% 2.26/2.48    (![A:$i,B:$i]:
% 2.26/2.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.26/2.48       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 2.26/2.48  thf('85', plain,
% 2.26/2.48      (![X30 : $i, X31 : $i]:
% 2.26/2.48         (~ (v1_subset_1 @ X31 @ X30)
% 2.26/2.48          | ((X31) != (X30))
% 2.26/2.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 2.26/2.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 2.26/2.48  thf('86', plain,
% 2.26/2.48      (![X30 : $i]:
% 2.26/2.48         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X30))
% 2.26/2.48          | ~ (v1_subset_1 @ X30 @ X30))),
% 2.26/2.48      inference('simplify', [status(thm)], ['85'])).
% 2.26/2.48  thf(dt_k2_subset_1, axiom,
% 2.26/2.48    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.26/2.48  thf('87', plain,
% 2.26/2.48      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 2.26/2.48      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 2.26/2.48  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.26/2.48  thf('88', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 2.26/2.48      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.26/2.48  thf('89', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 2.26/2.48      inference('demod', [status(thm)], ['87', '88'])).
% 2.26/2.48  thf('90', plain, (![X30 : $i]: ~ (v1_subset_1 @ X30 @ X30)),
% 2.26/2.48      inference('demod', [status(thm)], ['86', '89'])).
% 2.26/2.48  thf('91', plain,
% 2.26/2.48      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 2.26/2.48       ~ ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['84', '90'])).
% 2.26/2.48  thf('92', plain,
% 2.26/2.48      (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 2.26/2.48       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('split', [status(esa)], ['47'])).
% 2.26/2.48  thf('93', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A))))),
% 2.26/2.48      inference('clc', [status(thm)], ['6', '7'])).
% 2.26/2.48  thf('94', plain,
% 2.26/2.48      (((v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A) | (v1_xboole_0 @ sk_B_2))),
% 2.26/2.48      inference('clc', [status(thm)], ['35', '36'])).
% 2.26/2.48  thf('95', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2)
% 2.26/2.48        | ((sk_B_2) = (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A))))),
% 2.26/2.48      inference('clc', [status(thm)], ['6', '7'])).
% 2.26/2.48  thf('96', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('97', plain,
% 2.26/2.48      (![X30 : $i, X31 : $i]:
% 2.26/2.48         (((X31) = (X30))
% 2.26/2.48          | (v1_subset_1 @ X31 @ X30)
% 2.26/2.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 2.26/2.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 2.26/2.48  thf('98', plain,
% 2.26/2.48      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 2.26/2.48        | ((sk_B_2) = (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['96', '97'])).
% 2.26/2.48  thf('99', plain,
% 2.26/2.48      ((~ (v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('split', [status(esa)], ['47'])).
% 2.26/2.48  thf('100', plain,
% 2.26/2.48      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['98', '99'])).
% 2.26/2.48  thf('101', plain,
% 2.26/2.48      (![X20 : $i, X21 : $i]:
% 2.26/2.48         (~ (v2_pre_topc @ X21)
% 2.26/2.48          | ~ (l1_pre_topc @ X21)
% 2.26/2.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 2.26/2.48               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 2.26/2.48          | (v4_pre_topc @ (u1_struct_0 @ X20) @ X21)
% 2.26/2.48          | ~ (v1_borsuk_1 @ X20 @ X21)
% 2.26/2.48          | ~ (m1_pre_topc @ X20 @ X21))),
% 2.26/2.48      inference('simplify', [status(thm)], ['21'])).
% 2.26/2.48  thf('102', plain,
% 2.26/2.48      ((![X0 : $i]:
% 2.26/2.48          (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ sk_B_2))
% 2.26/2.48           | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.26/2.48           | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 2.26/2.48           | (v4_pre_topc @ (u1_struct_0 @ X0) @ sk_A)
% 2.26/2.48           | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48           | ~ (v2_pre_topc @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['100', '101'])).
% 2.26/2.48  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('105', plain,
% 2.26/2.48      ((![X0 : $i]:
% 2.26/2.48          (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ sk_B_2))
% 2.26/2.48           | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.26/2.48           | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 2.26/2.48           | (v4_pre_topc @ (u1_struct_0 @ X0) @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('demod', [status(thm)], ['102', '103', '104'])).
% 2.26/2.48  thf('106', plain,
% 2.26/2.48      (((~ (m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_B_2))
% 2.26/2.48         | (v1_xboole_0 @ sk_B_2)
% 2.26/2.48         | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 2.26/2.48         | ~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48         | ~ (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['95', '105'])).
% 2.26/2.48  thf('107', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 2.26/2.48      inference('demod', [status(thm)], ['87', '88'])).
% 2.26/2.48  thf('108', plain,
% 2.26/2.48      ((((v1_xboole_0 @ sk_B_2)
% 2.26/2.48         | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 2.26/2.48         | ~ (v1_borsuk_1 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48         | ~ (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('demod', [status(thm)], ['106', '107'])).
% 2.26/2.48  thf('109', plain,
% 2.26/2.48      ((((v1_xboole_0 @ sk_B_2)
% 2.26/2.48         | ~ (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48         | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 2.26/2.48         | (v1_xboole_0 @ sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['94', '108'])).
% 2.26/2.48  thf('110', plain,
% 2.26/2.48      ((((v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)
% 2.26/2.48         | ~ (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A)
% 2.26/2.48         | (v1_xboole_0 @ sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('simplify', [status(thm)], ['109'])).
% 2.26/2.48  thf('111', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2) | (m1_pre_topc @ (sk_C @ sk_B_2 @ sk_A) @ sk_A))),
% 2.26/2.48      inference('clc', [status(thm)], ['13', '14'])).
% 2.26/2.48  thf('112', plain,
% 2.26/2.48      ((((v1_xboole_0 @ sk_B_2)
% 2.26/2.48         | (v4_pre_topc @ (u1_struct_0 @ (sk_C @ sk_B_2 @ sk_A)) @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('clc', [status(thm)], ['110', '111'])).
% 2.26/2.48  thf('113', plain,
% 2.26/2.48      ((((v4_pre_topc @ sk_B_2 @ sk_A)
% 2.26/2.48         | (v1_xboole_0 @ sk_B_2)
% 2.26/2.48         | (v1_xboole_0 @ sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup+', [status(thm)], ['93', '112'])).
% 2.26/2.48  thf('114', plain,
% 2.26/2.48      ((((v1_xboole_0 @ sk_B_2) | (v4_pre_topc @ sk_B_2 @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('simplify', [status(thm)], ['113'])).
% 2.26/2.48  thf('115', plain,
% 2.26/2.48      ((((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))
% 2.26/2.48        | ~ (v4_pre_topc @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('demod', [status(thm)], ['43', '44'])).
% 2.26/2.48  thf('116', plain,
% 2.26/2.48      ((((v1_xboole_0 @ sk_B_2) | ((k2_pre_topc @ sk_A @ sk_B_2) = (sk_B_2))))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['114', '115'])).
% 2.26/2.48  thf('117', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('118', plain,
% 2.26/2.48      (![X28 : $i, X29 : $i]:
% 2.26/2.48         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 2.26/2.48          | ((k2_pre_topc @ X29 @ X28) != (u1_struct_0 @ X29))
% 2.26/2.48          | (v1_tops_1 @ X28 @ X29)
% 2.26/2.48          | ~ (l1_pre_topc @ X29))),
% 2.26/2.48      inference('cnf', [status(esa)], [d2_tops_3])).
% 2.26/2.48  thf('119', plain,
% 2.26/2.48      ((~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | (v1_tops_1 @ sk_B_2 @ sk_A)
% 2.26/2.48        | ((k2_pre_topc @ sk_A @ sk_B_2) != (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['117', '118'])).
% 2.26/2.48  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('121', plain,
% 2.26/2.48      (((v1_tops_1 @ sk_B_2 @ sk_A)
% 2.26/2.48        | ((k2_pre_topc @ sk_A @ sk_B_2) != (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('demod', [status(thm)], ['119', '120'])).
% 2.26/2.48  thf('122', plain,
% 2.26/2.48      (((((sk_B_2) != (u1_struct_0 @ sk_A))
% 2.26/2.48         | (v1_xboole_0 @ sk_B_2)
% 2.26/2.48         | (v1_tops_1 @ sk_B_2 @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['116', '121'])).
% 2.26/2.48  thf('123', plain,
% 2.26/2.48      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['98', '99'])).
% 2.26/2.48  thf('124', plain,
% 2.26/2.48      (((((sk_B_2) != (sk_B_2))
% 2.26/2.48         | (v1_xboole_0 @ sk_B_2)
% 2.26/2.48         | (v1_tops_1 @ sk_B_2 @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('demod', [status(thm)], ['122', '123'])).
% 2.26/2.48  thf('125', plain,
% 2.26/2.48      ((((v1_tops_1 @ sk_B_2 @ sk_A) | (v1_xboole_0 @ sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('simplify', [status(thm)], ['124'])).
% 2.26/2.48  thf('126', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf(t48_tex_2, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.48           ( ( ( v1_tops_1 @ B @ A ) & ( v2_tex_2 @ B @ A ) ) =>
% 2.26/2.48             ( v3_tex_2 @ B @ A ) ) ) ) ))).
% 2.26/2.48  thf('127', plain,
% 2.26/2.48      (![X44 : $i, X45 : $i]:
% 2.26/2.48         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 2.26/2.48          | (v3_tex_2 @ X44 @ X45)
% 2.26/2.48          | ~ (v2_tex_2 @ X44 @ X45)
% 2.26/2.48          | ~ (v1_tops_1 @ X44 @ X45)
% 2.26/2.48          | ~ (l1_pre_topc @ X45)
% 2.26/2.48          | ~ (v2_pre_topc @ X45)
% 2.26/2.48          | (v2_struct_0 @ X45))),
% 2.26/2.48      inference('cnf', [status(esa)], [t48_tex_2])).
% 2.26/2.48  thf('128', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | ~ (v1_tops_1 @ sk_B_2 @ sk_A)
% 2.26/2.48        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 2.26/2.48        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['126', '127'])).
% 2.26/2.48  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('131', plain,
% 2.26/2.48      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf(t43_tex_2, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 2.26/2.48         ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.26/2.48           ( v2_tex_2 @ B @ A ) ) ) ))).
% 2.26/2.48  thf('132', plain,
% 2.26/2.48      (![X38 : $i, X39 : $i]:
% 2.26/2.48         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 2.26/2.48          | (v2_tex_2 @ X38 @ X39)
% 2.26/2.48          | ~ (l1_pre_topc @ X39)
% 2.26/2.48          | ~ (v1_tdlat_3 @ X39)
% 2.26/2.48          | ~ (v2_pre_topc @ X39)
% 2.26/2.48          | (v2_struct_0 @ X39))),
% 2.26/2.48      inference('cnf', [status(esa)], [t43_tex_2])).
% 2.26/2.48  thf('133', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (v2_pre_topc @ sk_A)
% 2.26/2.48        | ~ (v1_tdlat_3 @ sk_A)
% 2.26/2.48        | ~ (l1_pre_topc @ sk_A)
% 2.26/2.48        | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['131', '132'])).
% 2.26/2.48  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('135', plain, ((v1_tdlat_3 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('137', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 2.26/2.48  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('139', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 2.26/2.48      inference('clc', [status(thm)], ['137', '138'])).
% 2.26/2.48  thf('140', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A)
% 2.26/2.48        | ~ (v1_tops_1 @ sk_B_2 @ sk_A)
% 2.26/2.48        | (v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('demod', [status(thm)], ['128', '129', '130', '139'])).
% 2.26/2.48  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('142', plain,
% 2.26/2.48      (((v3_tex_2 @ sk_B_2 @ sk_A) | ~ (v1_tops_1 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('clc', [status(thm)], ['140', '141'])).
% 2.26/2.48  thf('143', plain,
% 2.26/2.48      ((((v1_xboole_0 @ sk_B_2) | (v3_tex_2 @ sk_B_2 @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['125', '142'])).
% 2.26/2.48  thf('144', plain,
% 2.26/2.48      ((~ (v3_tex_2 @ sk_B_2 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('split', [status(esa)], ['0'])).
% 2.26/2.48  thf('145', plain,
% 2.26/2.48      (((v1_xboole_0 @ sk_B_2))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 2.26/2.48             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['143', '144'])).
% 2.26/2.48  thf(dt_k1_subset_1, axiom,
% 2.26/2.48    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.26/2.48  thf('146', plain,
% 2.26/2.48      (![X5 : $i]: (m1_subset_1 @ (k1_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 2.26/2.48      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 2.26/2.48  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 2.26/2.48  thf('147', plain, (![X3 : $i]: ((k1_subset_1 @ X3) = (k1_xboole_0))),
% 2.26/2.48      inference('cnf', [status(esa)], [d3_subset_1])).
% 2.26/2.48  thf('148', plain,
% 2.26/2.48      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 2.26/2.48      inference('demod', [status(thm)], ['146', '147'])).
% 2.26/2.48  thf('149', plain,
% 2.26/2.48      (![X30 : $i, X31 : $i]:
% 2.26/2.48         (((X31) = (X30))
% 2.26/2.48          | (v1_subset_1 @ X31 @ X30)
% 2.26/2.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 2.26/2.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 2.26/2.48  thf('150', plain,
% 2.26/2.48      (![X0 : $i]: ((v1_subset_1 @ k1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['148', '149'])).
% 2.26/2.48  thf('151', plain,
% 2.26/2.48      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 2.26/2.48      inference('demod', [status(thm)], ['146', '147'])).
% 2.26/2.48  thf(cc4_subset_1, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( v1_xboole_0 @ A ) =>
% 2.26/2.48       ( ![B:$i]:
% 2.26/2.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.26/2.48           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 2.26/2.48  thf('152', plain,
% 2.26/2.48      (![X12 : $i, X13 : $i]:
% 2.26/2.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 2.26/2.48          | ~ (v1_subset_1 @ X12 @ X13)
% 2.26/2.48          | ~ (v1_xboole_0 @ X13))),
% 2.26/2.48      inference('cnf', [status(esa)], [cc4_subset_1])).
% 2.26/2.48  thf('153', plain,
% 2.26/2.48      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_subset_1 @ k1_xboole_0 @ X0))),
% 2.26/2.48      inference('sup-', [status(thm)], ['151', '152'])).
% 2.26/2.48  thf('154', plain,
% 2.26/2.48      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.26/2.48      inference('sup-', [status(thm)], ['150', '153'])).
% 2.26/2.48  thf('155', plain,
% 2.26/2.48      ((((k1_xboole_0) = (sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 2.26/2.48             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['145', '154'])).
% 2.26/2.48  thf('156', plain,
% 2.26/2.48      ((((sk_B_2) = (u1_struct_0 @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['98', '99'])).
% 2.26/2.48  thf(rc3_tops_1, axiom,
% 2.26/2.48    (![A:$i]:
% 2.26/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.26/2.48       ( ?[B:$i]:
% 2.26/2.48         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 2.26/2.48           ( ~( v1_xboole_0 @ B ) ) & 
% 2.26/2.48           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.26/2.48  thf('157', plain,
% 2.26/2.48      (![X19 : $i]:
% 2.26/2.48         ((m1_subset_1 @ (sk_B @ X19) @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.26/2.48          | ~ (l1_pre_topc @ X19)
% 2.26/2.48          | ~ (v2_pre_topc @ X19)
% 2.26/2.48          | (v2_struct_0 @ X19))),
% 2.26/2.48      inference('cnf', [status(esa)], [rc3_tops_1])).
% 2.26/2.48  thf('158', plain,
% 2.26/2.48      ((((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))
% 2.26/2.48         | (v2_struct_0 @ sk_A)
% 2.26/2.48         | ~ (v2_pre_topc @ sk_A)
% 2.26/2.48         | ~ (l1_pre_topc @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup+', [status(thm)], ['156', '157'])).
% 2.26/2.48  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('161', plain,
% 2.26/2.48      ((((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_2))
% 2.26/2.48         | (v2_struct_0 @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('demod', [status(thm)], ['158', '159', '160'])).
% 2.26/2.48  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('163', plain,
% 2.26/2.48      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('clc', [status(thm)], ['161', '162'])).
% 2.26/2.48  thf('164', plain,
% 2.26/2.48      (![X30 : $i, X31 : $i]:
% 2.26/2.48         (((X31) = (X30))
% 2.26/2.48          | (v1_subset_1 @ X31 @ X30)
% 2.26/2.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 2.26/2.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 2.26/2.48  thf('165', plain,
% 2.26/2.48      ((((v1_subset_1 @ (sk_B @ sk_A) @ sk_B_2) | ((sk_B @ sk_A) = (sk_B_2))))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['163', '164'])).
% 2.26/2.48  thf('166', plain,
% 2.26/2.48      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('clc', [status(thm)], ['161', '162'])).
% 2.26/2.48  thf('167', plain,
% 2.26/2.48      (![X12 : $i, X13 : $i]:
% 2.26/2.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 2.26/2.48          | ~ (v1_subset_1 @ X12 @ X13)
% 2.26/2.48          | ~ (v1_xboole_0 @ X13))),
% 2.26/2.48      inference('cnf', [status(esa)], [cc4_subset_1])).
% 2.26/2.48  thf('168', plain,
% 2.26/2.48      (((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_subset_1 @ (sk_B @ sk_A) @ sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['166', '167'])).
% 2.26/2.48  thf('169', plain,
% 2.26/2.48      (((((sk_B @ sk_A) = (sk_B_2)) | ~ (v1_xboole_0 @ sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))),
% 2.26/2.48      inference('sup-', [status(thm)], ['165', '168'])).
% 2.26/2.48  thf('170', plain,
% 2.26/2.48      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B @ sk_A) = (sk_B_2))))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 2.26/2.48             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['155', '169'])).
% 2.26/2.48  thf('171', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 2.26/2.48      inference('demod', [status(thm)], ['87', '88'])).
% 2.26/2.48  thf(t3_subset, axiom,
% 2.26/2.48    (![A:$i,B:$i]:
% 2.26/2.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.26/2.48  thf('172', plain,
% 2.26/2.48      (![X14 : $i, X15 : $i]:
% 2.26/2.48         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 2.26/2.48      inference('cnf', [status(esa)], [t3_subset])).
% 2.26/2.48  thf('173', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.26/2.48      inference('sup-', [status(thm)], ['171', '172'])).
% 2.26/2.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.26/2.48  thf('174', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.26/2.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.26/2.48  thf(t69_xboole_1, axiom,
% 2.26/2.48    (![A:$i,B:$i]:
% 2.26/2.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.26/2.48       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 2.26/2.48  thf('175', plain,
% 2.26/2.48      (![X1 : $i, X2 : $i]:
% 2.26/2.48         (~ (r1_xboole_0 @ X1 @ X2)
% 2.26/2.48          | ~ (r1_tarski @ X1 @ X2)
% 2.26/2.48          | (v1_xboole_0 @ X1))),
% 2.26/2.48      inference('cnf', [status(esa)], [t69_xboole_1])).
% 2.26/2.48  thf('176', plain,
% 2.26/2.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 2.26/2.48      inference('sup-', [status(thm)], ['174', '175'])).
% 2.26/2.48  thf('177', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.26/2.48      inference('sup-', [status(thm)], ['173', '176'])).
% 2.26/2.48  thf('178', plain,
% 2.26/2.48      ((((k1_xboole_0) = (sk_B_2)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 2.26/2.48             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['145', '154'])).
% 2.26/2.48  thf('179', plain,
% 2.26/2.48      ((((sk_B @ sk_A) = (k1_xboole_0)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 2.26/2.48             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('demod', [status(thm)], ['170', '177', '178'])).
% 2.26/2.48  thf('180', plain,
% 2.26/2.48      (![X19 : $i]:
% 2.26/2.48         (~ (v1_xboole_0 @ (sk_B @ X19))
% 2.26/2.48          | ~ (l1_pre_topc @ X19)
% 2.26/2.48          | ~ (v2_pre_topc @ X19)
% 2.26/2.48          | (v2_struct_0 @ X19))),
% 2.26/2.48      inference('cnf', [status(esa)], [rc3_tops_1])).
% 2.26/2.48  thf('181', plain,
% 2.26/2.48      (((~ (v1_xboole_0 @ k1_xboole_0)
% 2.26/2.48         | (v2_struct_0 @ sk_A)
% 2.26/2.48         | ~ (v2_pre_topc @ sk_A)
% 2.26/2.48         | ~ (l1_pre_topc @ sk_A)))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 2.26/2.48             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('sup-', [status(thm)], ['179', '180'])).
% 2.26/2.48  thf('182', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.26/2.48      inference('sup-', [status(thm)], ['173', '176'])).
% 2.26/2.48  thf('183', plain, ((v2_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('184', plain, ((l1_pre_topc @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('185', plain,
% 2.26/2.48      (((v2_struct_0 @ sk_A))
% 2.26/2.48         <= (~ ((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) & 
% 2.26/2.48             ~ ((v3_tex_2 @ sk_B_2 @ sk_A)))),
% 2.26/2.48      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 2.26/2.48  thf('186', plain, (~ (v2_struct_0 @ sk_A)),
% 2.26/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.48  thf('187', plain,
% 2.26/2.48      (((v1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))) | 
% 2.26/2.48       ((v3_tex_2 @ sk_B_2 @ sk_A))),
% 2.26/2.48      inference('sup-', [status(thm)], ['185', '186'])).
% 2.26/2.48  thf('188', plain, ($false),
% 2.26/2.48      inference('sat_resolution*', [status(thm)], ['1', '91', '92', '187'])).
% 2.26/2.48  
% 2.26/2.48  % SZS output end Refutation
% 2.26/2.48  
% 2.26/2.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
