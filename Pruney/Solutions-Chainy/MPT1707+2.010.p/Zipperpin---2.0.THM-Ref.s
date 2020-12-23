%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.leUjbMiLGB

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:12 EST 2020

% Result     : Theorem 53.75s
% Output     : Refutation 53.75s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 414 expanded)
%              Number of leaves         :   30 ( 123 expanded)
%              Depth                    :   32
%              Number of atoms          : 2008 (9073 expanded)
%              Number of equality atoms :   18 ( 302 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t16_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                 => ~ ( ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                         => ( E != D ) )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) )
                         => ( E != D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                   => ~ ( ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                           => ( E != D ) )
                        & ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) )
                           => ( E != D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X28 @ X27 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v2_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_pre_topc @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_tmap_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( m1_connsp_2 @ ( sk_C @ X19 @ X18 ) @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('22',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('28',plain,
    ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['24'])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_connsp_2 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ~ ( m1_connsp_2 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ~ ( m1_connsp_2 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_D_1 )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_connsp_2 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( v2_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ sk_D_1 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_D_1 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X28 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_pre_topc @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( D
                      = ( k1_tsep_1 @ A @ B @ C ) )
                  <=> ( ( u1_struct_0 @ D )
                      = ( k2_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( v1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( X25
       != ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( ( u1_struct_0 @ X25 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('59',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) @ X24 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('72',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('73',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_C @ sk_D_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','79'])).

thf('81',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X28 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('89',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('92',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X33: $i] :
      ( ( X33 != sk_D_1 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    ! [X34: $i] :
      ( ( X34 != sk_D_1 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['0','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.leUjbMiLGB
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:35:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 53.75/53.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 53.75/53.96  % Solved by: fo/fo7.sh
% 53.75/53.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 53.75/53.96  % done 13665 iterations in 53.514s
% 53.75/53.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 53.75/53.96  % SZS output start Refutation
% 53.75/53.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 53.75/53.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 53.75/53.96  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 53.75/53.96  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 53.75/53.96  thf(sk_A_type, type, sk_A: $i).
% 53.75/53.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 53.75/53.96  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 53.75/53.96  thf(sk_B_type, type, sk_B: $i).
% 53.75/53.96  thf(sk_C_1_type, type, sk_C_1: $i).
% 53.75/53.96  thf(sk_D_1_type, type, sk_D_1: $i).
% 53.75/53.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 53.75/53.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 53.75/53.96  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 53.75/53.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 53.75/53.96  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 53.75/53.96  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 53.75/53.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 53.75/53.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 53.75/53.96  thf(t16_tmap_1, conjecture,
% 53.75/53.96    (![A:$i]:
% 53.75/53.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 53.75/53.96       ( ![B:$i]:
% 53.75/53.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 53.75/53.96           ( ![C:$i]:
% 53.75/53.96             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 53.75/53.96               ( ![D:$i]:
% 53.75/53.96                 ( ( m1_subset_1 @
% 53.75/53.96                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 53.75/53.96                   ( ~( ( ![E:$i]:
% 53.75/53.96                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 53.75/53.96                            ( ( E ) != ( D ) ) ) ) & 
% 53.75/53.96                        ( ![E:$i]:
% 53.75/53.96                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 53.75/53.96                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 53.75/53.96  thf(zf_stmt_0, negated_conjecture,
% 53.75/53.96    (~( ![A:$i]:
% 53.75/53.96        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 53.75/53.96            ( l1_pre_topc @ A ) ) =>
% 53.75/53.96          ( ![B:$i]:
% 53.75/53.96            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 53.75/53.96              ( ![C:$i]:
% 53.75/53.96                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 53.75/53.96                  ( ![D:$i]:
% 53.75/53.96                    ( ( m1_subset_1 @
% 53.75/53.96                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 53.75/53.96                      ( ~( ( ![E:$i]:
% 53.75/53.96                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 53.75/53.96                               ( ( E ) != ( D ) ) ) ) & 
% 53.75/53.96                           ( ![E:$i]:
% 53.75/53.96                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 53.75/53.96                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 53.75/53.96    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 53.75/53.96  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('1', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf(dt_k1_tsep_1, axiom,
% 53.75/53.96    (![A:$i,B:$i,C:$i]:
% 53.75/53.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 53.75/53.96         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 53.75/53.96         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 53.75/53.96       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 53.75/53.96         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 53.75/53.96         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 53.75/53.96  thf('3', plain,
% 53.75/53.96      (![X27 : $i, X28 : $i, X29 : $i]:
% 53.75/53.96         (~ (m1_pre_topc @ X27 @ X28)
% 53.75/53.96          | (v2_struct_0 @ X27)
% 53.75/53.96          | ~ (l1_pre_topc @ X28)
% 53.75/53.96          | (v2_struct_0 @ X28)
% 53.75/53.96          | (v2_struct_0 @ X29)
% 53.75/53.96          | ~ (m1_pre_topc @ X29 @ X28)
% 53.75/53.96          | (m1_pre_topc @ (k1_tsep_1 @ X28 @ X27 @ X29) @ X28))),
% 53.75/53.96      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 53.75/53.96  thf('4', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 53.75/53.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ X0)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | ~ (l1_pre_topc @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('sup-', [status(thm)], ['2', '3'])).
% 53.75/53.96  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('6', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 53.75/53.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ X0)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('demod', [status(thm)], ['4', '5'])).
% 53.75/53.96  thf('7', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 53.75/53.96      inference('sup-', [status(thm)], ['1', '6'])).
% 53.75/53.96  thf(dt_m1_pre_topc, axiom,
% 53.75/53.96    (![A:$i]:
% 53.75/53.96     ( ( l1_pre_topc @ A ) =>
% 53.75/53.96       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 53.75/53.96  thf('8', plain,
% 53.75/53.96      (![X13 : $i, X14 : $i]:
% 53.75/53.96         (~ (m1_pre_topc @ X13 @ X14)
% 53.75/53.96          | (l1_pre_topc @ X13)
% 53.75/53.96          | ~ (l1_pre_topc @ X14))),
% 53.75/53.96      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 53.75/53.96  thf('9', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B)
% 53.75/53.96        | ~ (l1_pre_topc @ sk_A)
% 53.75/53.96        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('sup-', [status(thm)], ['7', '8'])).
% 53.75/53.96  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('11', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B)
% 53.75/53.96        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('demod', [status(thm)], ['9', '10'])).
% 53.75/53.96  thf('12', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('13', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf(fc1_tmap_1, axiom,
% 53.75/53.96    (![A:$i,B:$i,C:$i]:
% 53.75/53.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 53.75/53.96         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 53.75/53.96         ( m1_pre_topc @ B @ A ) & ( ~( v2_struct_0 @ C ) ) & 
% 53.75/53.96         ( m1_pre_topc @ C @ A ) ) =>
% 53.75/53.96       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 53.75/53.96         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 53.75/53.96         ( v2_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) ) ))).
% 53.75/53.96  thf('14', plain,
% 53.75/53.96      (![X30 : $i, X31 : $i, X32 : $i]:
% 53.75/53.96         (~ (m1_pre_topc @ X30 @ X31)
% 53.75/53.96          | (v2_struct_0 @ X30)
% 53.75/53.96          | ~ (l1_pre_topc @ X31)
% 53.75/53.96          | ~ (v2_pre_topc @ X31)
% 53.75/53.96          | (v2_struct_0 @ X31)
% 53.75/53.96          | (v2_struct_0 @ X32)
% 53.75/53.96          | ~ (m1_pre_topc @ X32 @ X31)
% 53.75/53.96          | (v2_pre_topc @ (k1_tsep_1 @ X31 @ X30 @ X32)))),
% 53.75/53.96      inference('cnf', [status(esa)], [fc1_tmap_1])).
% 53.75/53.96  thf('15', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 53.75/53.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ X0)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | ~ (v2_pre_topc @ sk_A)
% 53.75/53.96          | ~ (l1_pre_topc @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('sup-', [status(thm)], ['13', '14'])).
% 53.75/53.96  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('18', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 53.75/53.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ X0)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('demod', [status(thm)], ['15', '16', '17'])).
% 53.75/53.96  thf('19', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('sup-', [status(thm)], ['12', '18'])).
% 53.75/53.96  thf('20', plain,
% 53.75/53.96      ((m1_subset_1 @ sk_D_1 @ 
% 53.75/53.96        (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf(existence_m1_connsp_2, axiom,
% 53.75/53.96    (![A:$i,B:$i]:
% 53.75/53.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 53.75/53.96         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 53.75/53.96       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 53.75/53.96  thf('21', plain,
% 53.75/53.96      (![X18 : $i, X19 : $i]:
% 53.75/53.96         (~ (l1_pre_topc @ X18)
% 53.75/53.96          | ~ (v2_pre_topc @ X18)
% 53.75/53.96          | (v2_struct_0 @ X18)
% 53.75/53.96          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 53.75/53.96          | (m1_connsp_2 @ (sk_C @ X19 @ X18) @ X18 @ X19))),
% 53.75/53.96      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 53.75/53.96  thf('22', plain,
% 53.75/53.96      (((m1_connsp_2 @ (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96         (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1)
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('sup-', [status(thm)], ['20', '21'])).
% 53.75/53.96  thf('23', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B)
% 53.75/53.96        | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (m1_connsp_2 @ 
% 53.75/53.96           (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96           (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1))),
% 53.75/53.96      inference('sup-', [status(thm)], ['19', '22'])).
% 53.75/53.96  thf('24', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (m1_connsp_2 @ 
% 53.75/53.96           (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96           (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1)
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1))),
% 53.75/53.96      inference('sup-', [status(thm)], ['11', '23'])).
% 53.75/53.96  thf('25', plain,
% 53.75/53.96      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (m1_connsp_2 @ 
% 53.75/53.96           (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96           (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('simplify', [status(thm)], ['24'])).
% 53.75/53.96  thf('26', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('sup-', [status(thm)], ['12', '18'])).
% 53.75/53.96  thf('27', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B)
% 53.75/53.96        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('demod', [status(thm)], ['9', '10'])).
% 53.75/53.96  thf('28', plain,
% 53.75/53.96      (((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (m1_connsp_2 @ 
% 53.75/53.96           (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96           (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('simplify', [status(thm)], ['24'])).
% 53.75/53.96  thf('29', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B)
% 53.75/53.96        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('demod', [status(thm)], ['9', '10'])).
% 53.75/53.96  thf('30', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('sup-', [status(thm)], ['12', '18'])).
% 53.75/53.96  thf('31', plain,
% 53.75/53.96      ((m1_subset_1 @ sk_D_1 @ 
% 53.75/53.96        (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf(dt_m1_connsp_2, axiom,
% 53.75/53.96    (![A:$i,B:$i]:
% 53.75/53.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 53.75/53.96         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 53.75/53.96       ( ![C:$i]:
% 53.75/53.96         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 53.75/53.96           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 53.75/53.96  thf('32', plain,
% 53.75/53.96      (![X15 : $i, X16 : $i, X17 : $i]:
% 53.75/53.96         (~ (l1_pre_topc @ X15)
% 53.75/53.96          | ~ (v2_pre_topc @ X15)
% 53.75/53.96          | (v2_struct_0 @ X15)
% 53.75/53.96          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 53.75/53.96          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 53.75/53.96          | ~ (m1_connsp_2 @ X17 @ X15 @ X16))),
% 53.75/53.96      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 53.75/53.96  thf('33', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         (~ (m1_connsp_2 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1)
% 53.75/53.96          | (m1_subset_1 @ X0 @ 
% 53.75/53.96             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('sup-', [status(thm)], ['31', '32'])).
% 53.75/53.96  thf('34', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v2_struct_0 @ sk_C_1)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B)
% 53.75/53.96          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (m1_subset_1 @ X0 @ 
% 53.75/53.96             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))
% 53.75/53.96          | ~ (m1_connsp_2 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1))),
% 53.75/53.96      inference('sup-', [status(thm)], ['30', '33'])).
% 53.75/53.96  thf('35', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v2_struct_0 @ sk_B)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_C_1)
% 53.75/53.96          | ~ (m1_connsp_2 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1)
% 53.75/53.96          | (m1_subset_1 @ X0 @ 
% 53.75/53.96             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (v2_struct_0 @ sk_B)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_C_1))),
% 53.75/53.96      inference('sup-', [status(thm)], ['29', '34'])).
% 53.75/53.96  thf('36', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (m1_subset_1 @ X0 @ 
% 53.75/53.96             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))
% 53.75/53.96          | ~ (m1_connsp_2 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_D_1)
% 53.75/53.96          | (v2_struct_0 @ sk_C_1)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('simplify', [status(thm)], ['35'])).
% 53.75/53.96  thf('37', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (m1_subset_1 @ 
% 53.75/53.96           (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96           (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('sup-', [status(thm)], ['28', '36'])).
% 53.75/53.96  thf('38', plain,
% 53.75/53.96      (((m1_subset_1 @ (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('simplify', [status(thm)], ['37'])).
% 53.75/53.96  thf(t6_connsp_2, axiom,
% 53.75/53.96    (![A:$i]:
% 53.75/53.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 53.75/53.96       ( ![B:$i]:
% 53.75/53.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 53.75/53.96           ( ![C:$i]:
% 53.75/53.96             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 53.75/53.96               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 53.75/53.96  thf('39', plain,
% 53.75/53.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 53.75/53.96         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 53.75/53.96          | ~ (m1_connsp_2 @ X20 @ X21 @ X22)
% 53.75/53.96          | (r2_hidden @ X22 @ X20)
% 53.75/53.96          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 53.75/53.96          | ~ (l1_pre_topc @ X21)
% 53.75/53.96          | ~ (v2_pre_topc @ X21)
% 53.75/53.96          | (v2_struct_0 @ X21))),
% 53.75/53.96      inference('cnf', [status(esa)], [t6_connsp_2])).
% 53.75/53.96  thf('40', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v2_struct_0 @ sk_B)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_C_1)
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | ~ (m1_subset_1 @ X0 @ 
% 53.75/53.96               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | (r2_hidden @ X0 @ 
% 53.75/53.96             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | ~ (m1_connsp_2 @ 
% 53.75/53.96               (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96               (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 53.75/53.96      inference('sup-', [status(thm)], ['38', '39'])).
% 53.75/53.96  thf('41', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         (~ (m1_connsp_2 @ 
% 53.75/53.96             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96             (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.75/53.96          | (r2_hidden @ X0 @ 
% 53.75/53.96             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | ~ (m1_subset_1 @ X0 @ 
% 53.75/53.96               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | ~ (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (v2_struct_0 @ sk_C_1)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('simplify', [status(thm)], ['40'])).
% 53.75/53.96  thf('42', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v2_struct_0 @ sk_B)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_C_1)
% 53.75/53.96          | (v2_struct_0 @ sk_B)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_C_1)
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | ~ (m1_subset_1 @ X0 @ 
% 53.75/53.96               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | (r2_hidden @ X0 @ 
% 53.75/53.96             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | ~ (m1_connsp_2 @ 
% 53.75/53.96               (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96               (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 53.75/53.96      inference('sup-', [status(thm)], ['27', '41'])).
% 53.75/53.96  thf('43', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         (~ (m1_connsp_2 @ 
% 53.75/53.96             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96             (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.75/53.96          | (r2_hidden @ X0 @ 
% 53.75/53.96             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | ~ (m1_subset_1 @ X0 @ 
% 53.75/53.96               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | ~ (v2_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (v2_struct_0 @ sk_C_1)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('simplify', [status(thm)], ['42'])).
% 53.75/53.96  thf('44', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v2_struct_0 @ sk_C_1)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B)
% 53.75/53.96          | (v2_struct_0 @ sk_B)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_C_1)
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | ~ (m1_subset_1 @ X0 @ 
% 53.75/53.96               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | (r2_hidden @ X0 @ 
% 53.75/53.96             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | ~ (m1_connsp_2 @ 
% 53.75/53.96               (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96               (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 53.75/53.96      inference('sup-', [status(thm)], ['26', '43'])).
% 53.75/53.96  thf('45', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         (~ (m1_connsp_2 @ 
% 53.75/53.96             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.96             (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 53.75/53.96          | (r2_hidden @ X0 @ 
% 53.75/53.96             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | ~ (m1_subset_1 @ X0 @ 
% 53.75/53.96               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96          | (v2_struct_0 @ sk_B)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_C_1))),
% 53.75/53.96      inference('simplify', [status(thm)], ['44'])).
% 53.75/53.96  thf('46', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | ~ (m1_subset_1 @ sk_D_1 @ 
% 53.75/53.96             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96        | (r2_hidden @ sk_D_1 @ 
% 53.75/53.96           (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 53.75/53.96      inference('sup-', [status(thm)], ['25', '45'])).
% 53.75/53.96  thf('47', plain,
% 53.75/53.96      ((m1_subset_1 @ sk_D_1 @ 
% 53.75/53.96        (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('48', plain,
% 53.75/53.96      (((v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B)
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (r2_hidden @ sk_D_1 @ 
% 53.75/53.96           (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 53.75/53.96      inference('demod', [status(thm)], ['46', '47'])).
% 53.75/53.96  thf('49', plain,
% 53.75/53.96      (((r2_hidden @ sk_D_1 @ 
% 53.75/53.96         (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.96        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.96        | (v2_struct_0 @ sk_C_1)
% 53.75/53.96        | (v2_struct_0 @ sk_A)
% 53.75/53.96        | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('simplify', [status(thm)], ['48'])).
% 53.75/53.96  thf('50', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('51', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('52', plain,
% 53.75/53.96      (![X27 : $i, X28 : $i, X29 : $i]:
% 53.75/53.96         (~ (m1_pre_topc @ X27 @ X28)
% 53.75/53.96          | (v2_struct_0 @ X27)
% 53.75/53.96          | ~ (l1_pre_topc @ X28)
% 53.75/53.96          | (v2_struct_0 @ X28)
% 53.75/53.96          | (v2_struct_0 @ X29)
% 53.75/53.96          | ~ (m1_pre_topc @ X29 @ X28)
% 53.75/53.96          | (v1_pre_topc @ (k1_tsep_1 @ X28 @ X27 @ X29)))),
% 53.75/53.96      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 53.75/53.96  thf('53', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 53.75/53.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ X0)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | ~ (l1_pre_topc @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('sup-', [status(thm)], ['51', '52'])).
% 53.75/53.96  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 53.75/53.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.96  thf('55', plain,
% 53.75/53.96      (![X0 : $i]:
% 53.75/53.96         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 53.75/53.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ X0)
% 53.75/53.96          | (v2_struct_0 @ sk_A)
% 53.75/53.96          | (v2_struct_0 @ sk_B))),
% 53.75/53.96      inference('demod', [status(thm)], ['53', '54'])).
% 53.75/53.97  thf('56', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.97      inference('sup-', [status(thm)], ['50', '55'])).
% 53.75/53.97  thf('57', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 53.75/53.97      inference('sup-', [status(thm)], ['1', '6'])).
% 53.75/53.97  thf(d2_tsep_1, axiom,
% 53.75/53.97    (![A:$i]:
% 53.75/53.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 53.75/53.97       ( ![B:$i]:
% 53.75/53.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 53.75/53.97           ( ![C:$i]:
% 53.75/53.97             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 53.75/53.97               ( ![D:$i]:
% 53.75/53.97                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 53.75/53.97                     ( m1_pre_topc @ D @ A ) ) =>
% 53.75/53.97                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 53.75/53.97                     ( ( u1_struct_0 @ D ) =
% 53.75/53.97                       ( k2_xboole_0 @
% 53.75/53.97                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 53.75/53.97  thf('58', plain,
% 53.75/53.97      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 53.75/53.97         ((v2_struct_0 @ X23)
% 53.75/53.97          | ~ (m1_pre_topc @ X23 @ X24)
% 53.75/53.97          | (v2_struct_0 @ X25)
% 53.75/53.97          | ~ (v1_pre_topc @ X25)
% 53.75/53.97          | ~ (m1_pre_topc @ X25 @ X24)
% 53.75/53.97          | ((X25) != (k1_tsep_1 @ X24 @ X23 @ X26))
% 53.75/53.97          | ((u1_struct_0 @ X25)
% 53.75/53.97              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 53.75/53.97          | ~ (m1_pre_topc @ X26 @ X24)
% 53.75/53.97          | (v2_struct_0 @ X26)
% 53.75/53.97          | ~ (l1_pre_topc @ X24)
% 53.75/53.97          | (v2_struct_0 @ X24))),
% 53.75/53.97      inference('cnf', [status(esa)], [d2_tsep_1])).
% 53.75/53.97  thf('59', plain,
% 53.75/53.97      (![X23 : $i, X24 : $i, X26 : $i]:
% 53.75/53.97         ((v2_struct_0 @ X24)
% 53.75/53.97          | ~ (l1_pre_topc @ X24)
% 53.75/53.97          | (v2_struct_0 @ X26)
% 53.75/53.97          | ~ (m1_pre_topc @ X26 @ X24)
% 53.75/53.97          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 53.75/53.97              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 53.75/53.97          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 53.75/53.97          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 53.75/53.97          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 53.75/53.97          | ~ (m1_pre_topc @ X23 @ X24)
% 53.75/53.97          | (v2_struct_0 @ X23))),
% 53.75/53.97      inference('simplify', [status(thm)], ['58'])).
% 53.75/53.97  thf('60', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 53.75/53.97        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | ~ (l1_pre_topc @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_A))),
% 53.75/53.97      inference('sup-', [status(thm)], ['57', '59'])).
% 53.75/53.97  thf('61', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('62', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('64', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A))),
% 53.75/53.97      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 53.75/53.97  thf('65', plain,
% 53.75/53.97      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 53.75/53.97        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1))),
% 53.75/53.97      inference('simplify', [status(thm)], ['64'])).
% 53.75/53.97  thf('66', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))),
% 53.75/53.97      inference('sup-', [status(thm)], ['56', '65'])).
% 53.75/53.97  thf('67', plain,
% 53.75/53.97      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1))),
% 53.75/53.97      inference('simplify', [status(thm)], ['66'])).
% 53.75/53.97  thf('68', plain,
% 53.75/53.97      ((m1_subset_1 @ sk_D_1 @ 
% 53.75/53.97        (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf(t2_subset, axiom,
% 53.75/53.97    (![A:$i,B:$i]:
% 53.75/53.97     ( ( m1_subset_1 @ A @ B ) =>
% 53.75/53.97       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 53.75/53.97  thf('69', plain,
% 53.75/53.97      (![X8 : $i, X9 : $i]:
% 53.75/53.97         ((r2_hidden @ X8 @ X9)
% 53.75/53.97          | (v1_xboole_0 @ X9)
% 53.75/53.97          | ~ (m1_subset_1 @ X8 @ X9))),
% 53.75/53.97      inference('cnf', [status(esa)], [t2_subset])).
% 53.75/53.97  thf('70', plain,
% 53.75/53.97      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ 
% 53.75/53.97           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 53.75/53.97      inference('sup-', [status(thm)], ['68', '69'])).
% 53.75/53.97  thf('71', plain,
% 53.75/53.97      (((r2_hidden @ sk_D_1 @ 
% 53.75/53.97         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 53.75/53.97      inference('sup+', [status(thm)], ['67', '70'])).
% 53.75/53.97  thf(d3_xboole_0, axiom,
% 53.75/53.97    (![A:$i,B:$i,C:$i]:
% 53.75/53.97     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 53.75/53.97       ( ![D:$i]:
% 53.75/53.97         ( ( r2_hidden @ D @ C ) <=>
% 53.75/53.97           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 53.75/53.97  thf('72', plain,
% 53.75/53.97      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 53.75/53.97         (~ (r2_hidden @ X4 @ X2)
% 53.75/53.97          | (r2_hidden @ X4 @ X3)
% 53.75/53.97          | (r2_hidden @ X4 @ X1)
% 53.75/53.97          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 53.75/53.97      inference('cnf', [status(esa)], [d3_xboole_0])).
% 53.75/53.97  thf('73', plain,
% 53.75/53.97      (![X1 : $i, X3 : $i, X4 : $i]:
% 53.75/53.97         ((r2_hidden @ X4 @ X1)
% 53.75/53.97          | (r2_hidden @ X4 @ X3)
% 53.75/53.97          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 53.75/53.97      inference('simplify', [status(thm)], ['72'])).
% 53.75/53.97  thf('74', plain,
% 53.75/53.97      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C_1)))),
% 53.75/53.97      inference('sup-', [status(thm)], ['71', '73'])).
% 53.75/53.97  thf('75', plain,
% 53.75/53.97      (((m1_subset_1 @ (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 53.75/53.97         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B))),
% 53.75/53.97      inference('simplify', [status(thm)], ['37'])).
% 53.75/53.97  thf(t5_subset, axiom,
% 53.75/53.97    (![A:$i,B:$i,C:$i]:
% 53.75/53.97     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 53.75/53.97          ( v1_xboole_0 @ C ) ) ))).
% 53.75/53.97  thf('76', plain,
% 53.75/53.97      (![X10 : $i, X11 : $i, X12 : $i]:
% 53.75/53.97         (~ (r2_hidden @ X10 @ X11)
% 53.75/53.97          | ~ (v1_xboole_0 @ X12)
% 53.75/53.97          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 53.75/53.97      inference('cnf', [status(esa)], [t5_subset])).
% 53.75/53.97  thf('77', plain,
% 53.75/53.97      (![X0 : $i]:
% 53.75/53.97         ((v2_struct_0 @ sk_B)
% 53.75/53.97          | (v2_struct_0 @ sk_A)
% 53.75/53.97          | (v2_struct_0 @ sk_C_1)
% 53.75/53.97          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97          | ~ (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.97          | ~ (r2_hidden @ X0 @ 
% 53.75/53.97               (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 53.75/53.97      inference('sup-', [status(thm)], ['75', '76'])).
% 53.75/53.97  thf('78', plain,
% 53.75/53.97      (![X0 : $i]:
% 53.75/53.97         ((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 53.75/53.97          | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97          | (v2_struct_0 @ sk_C_1)
% 53.75/53.97          | (v2_struct_0 @ sk_A)
% 53.75/53.97          | (v2_struct_0 @ sk_B)
% 53.75/53.97          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97          | ~ (r2_hidden @ X0 @ 
% 53.75/53.97               (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.97          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97          | (v2_struct_0 @ sk_C_1)
% 53.75/53.97          | (v2_struct_0 @ sk_A)
% 53.75/53.97          | (v2_struct_0 @ sk_B))),
% 53.75/53.97      inference('sup-', [status(thm)], ['74', '77'])).
% 53.75/53.97  thf('79', plain,
% 53.75/53.97      (![X0 : $i]:
% 53.75/53.97         (~ (r2_hidden @ X0 @ 
% 53.75/53.97             (sk_C @ sk_D_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 53.75/53.97          | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97          | (v2_struct_0 @ sk_B)
% 53.75/53.97          | (v2_struct_0 @ sk_A)
% 53.75/53.97          | (v2_struct_0 @ sk_C_1)
% 53.75/53.97          | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97          | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C_1)))),
% 53.75/53.97      inference('simplify', [status(thm)], ['78'])).
% 53.75/53.97  thf('80', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 53.75/53.97      inference('sup-', [status(thm)], ['49', '79'])).
% 53.75/53.97  thf('81', plain,
% 53.75/53.97      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 53.75/53.97        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B))),
% 53.75/53.97      inference('simplify', [status(thm)], ['80'])).
% 53.75/53.97  thf('82', plain,
% 53.75/53.97      (![X27 : $i, X28 : $i, X29 : $i]:
% 53.75/53.97         (~ (m1_pre_topc @ X27 @ X28)
% 53.75/53.97          | (v2_struct_0 @ X27)
% 53.75/53.97          | ~ (l1_pre_topc @ X28)
% 53.75/53.97          | (v2_struct_0 @ X28)
% 53.75/53.97          | (v2_struct_0 @ X29)
% 53.75/53.97          | ~ (m1_pre_topc @ X29 @ X28)
% 53.75/53.97          | ~ (v2_struct_0 @ (k1_tsep_1 @ X28 @ X27 @ X29)))),
% 53.75/53.97      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 53.75/53.97  thf('83', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | ~ (l1_pre_topc @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 53.75/53.97      inference('sup-', [status(thm)], ['81', '82'])).
% 53.75/53.97  thf('84', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('86', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('87', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B))),
% 53.75/53.97      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 53.75/53.97  thf('88', plain,
% 53.75/53.97      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B))),
% 53.75/53.97      inference('simplify', [status(thm)], ['87'])).
% 53.75/53.97  thf(t1_subset, axiom,
% 53.75/53.97    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 53.75/53.97  thf('89', plain,
% 53.75/53.97      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 53.75/53.97      inference('cnf', [status(esa)], [t1_subset])).
% 53.75/53.97  thf('90', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1)))),
% 53.75/53.97      inference('sup-', [status(thm)], ['88', '89'])).
% 53.75/53.97  thf('91', plain,
% 53.75/53.97      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 53.75/53.97      inference('cnf', [status(esa)], [t1_subset])).
% 53.75/53.97  thf('92', plain,
% 53.75/53.97      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 53.75/53.97        | (v2_struct_0 @ sk_C_1)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 53.75/53.97      inference('sup-', [status(thm)], ['90', '91'])).
% 53.75/53.97  thf('93', plain,
% 53.75/53.97      (![X33 : $i]:
% 53.75/53.97         (((X33) != (sk_D_1)) | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_C_1)))),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('94', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1))),
% 53.75/53.97      inference('simplify', [status(thm)], ['93'])).
% 53.75/53.97  thf('95', plain,
% 53.75/53.97      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 53.75/53.97        | (v2_struct_0 @ sk_B)
% 53.75/53.97        | (v2_struct_0 @ sk_A)
% 53.75/53.97        | (v2_struct_0 @ sk_C_1))),
% 53.75/53.97      inference('sup-', [status(thm)], ['92', '94'])).
% 53.75/53.97  thf('96', plain,
% 53.75/53.97      (![X34 : $i]:
% 53.75/53.97         (((X34) != (sk_D_1)) | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_B)))),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('97', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 53.75/53.97      inference('simplify', [status(thm)], ['96'])).
% 53.75/53.97  thf('98', plain,
% 53.75/53.97      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 53.75/53.97      inference('sup-', [status(thm)], ['95', '97'])).
% 53.75/53.97  thf('99', plain, (~ (v2_struct_0 @ sk_C_1)),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('100', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 53.75/53.97      inference('clc', [status(thm)], ['98', '99'])).
% 53.75/53.97  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 53.75/53.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 53.75/53.97  thf('102', plain, ((v2_struct_0 @ sk_A)),
% 53.75/53.97      inference('clc', [status(thm)], ['100', '101'])).
% 53.75/53.97  thf('103', plain, ($false), inference('demod', [status(thm)], ['0', '102'])).
% 53.75/53.97  
% 53.75/53.97  % SZS output end Refutation
% 53.75/53.97  
% 53.75/53.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
