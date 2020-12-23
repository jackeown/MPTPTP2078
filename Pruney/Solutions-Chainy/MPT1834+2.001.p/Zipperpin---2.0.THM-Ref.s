%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qjo6hGOr6a

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:12 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  486 (1308 expanded)
%              Number of leaves         :   41 ( 349 expanded)
%              Depth                    :   47
%              Number of atoms          : 17935 (94398 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   32 (  12 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(r3_tsep_1_type,type,(
    r3_tsep_1: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t150_tmap_1,conjecture,(
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
             => ( ( r3_tsep_1 @ A @ B @ C )
              <=> ( ( r1_tsep_1 @ B @ C )
                  & ! [D: $i] :
                      ( ( ~ ( v2_struct_0 @ D )
                        & ( v2_pre_topc @ D )
                        & ( l1_pre_topc @ D ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) )
                            & ( v5_pre_topc @ E @ B @ D )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                                & ( v5_pre_topc @ F @ C @ D )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                             => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) )
                                & ( v1_funct_2 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                                & ( v5_pre_topc @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                                & ( m1_subset_1 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )).

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
               => ( ( r3_tsep_1 @ A @ B @ C )
                <=> ( ( r1_tsep_1 @ B @ C )
                    & ! [D: $i] :
                        ( ( ~ ( v2_struct_0 @ D )
                          & ( v2_pre_topc @ D )
                          & ( l1_pre_topc @ D ) )
                       => ! [E: $i] :
                            ( ( ( v1_funct_1 @ E )
                              & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ E @ B @ D )
                              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) )
                           => ! [F: $i] :
                                ( ( ( v1_funct_1 @ F )
                                  & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                                  & ( v5_pre_topc @ F @ C @ D )
                                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                               => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) )
                                  & ( v1_funct_2 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                                  & ( v5_pre_topc @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                                  & ( m1_subset_1 @ ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t150_tmap_1])).

thf('0',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t135_tmap_1,axiom,(
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
             => ( ( r3_tsep_1 @ A @ B @ C )
              <=> ( ( r1_tsep_1 @ B @ C )
                  & ! [D: $i] :
                      ( ( ~ ( v2_struct_0 @ D )
                        & ( v2_pre_topc @ D )
                        & ( l1_pre_topc @ D ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) )
                         => ( ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) )
                              & ( v1_funct_2 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ B @ D )
                              & ( m1_subset_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) )
                              & ( v1_funct_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) )
                              & ( v1_funct_2 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ C @ D )
                              & ( m1_subset_1 @ ( k3_tmap_1 @ A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                           => ( ( v1_funct_1 @ E )
                              & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) )
                              & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ( r1_tsep_1 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('4',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_funct_1 @ sk_F )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( l1_pre_topc @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( v2_pre_topc @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('31',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf(dt_k10_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A )
        & ~ ( v2_struct_0 @ D )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
        & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X25 @ X28 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X28 @ X25 @ X27 ) ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('36',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ X1 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ X1 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ sk_F )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['23','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf('44',plain,
    ( ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('63',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('65',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('66',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('67',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('68',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X25 @ X28 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X28 @ X25 @ X27 ) ) @ ( u1_struct_0 @ X26 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('71',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ X1 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ X1 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_1 @ sk_F )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['63','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['62','77'])).

thf('79',plain,
    ( ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['61','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['49'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t85_tsep_1,axiom,(
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
             => ( ( ( r1_tsep_1 @ B @ C )
                  & ( r4_tsep_1 @ A @ B @ C ) )
              <=> ( r3_tsep_1 @ A @ B @ C ) ) ) ) ) )).

thf('95',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( m1_pre_topc @ X41 @ X42 )
      | ~ ( r3_tsep_1 @ X42 @ X41 @ X43 )
      | ( r4_tsep_1 @ X42 @ X41 @ X43 )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t85_tsep_1])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r4_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('104',plain,
    ( ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
   <= ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['104'])).

thf('106',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('108',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('109',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('110',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('111',plain,
    ( ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
   <= ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('114',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf(t145_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( r1_tsep_1 @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ E @ C @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ F @ D @ B )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ( r4_tsep_1 @ A @ C @ D )
                             => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                                & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('115',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v5_pre_topc @ X38 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X37 @ X35 @ X39 @ X36 @ X40 @ X38 ) @ ( k1_tsep_1 @ X37 @ X39 @ X36 ) @ X35 )
      | ~ ( r4_tsep_1 @ X37 @ X39 @ X36 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v5_pre_topc @ X40 @ X39 @ X35 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( r1_tsep_1 @ X39 @ X36 )
      | ~ ( m1_pre_topc @ X39 @ X37 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t145_tmap_1])).

thf('116',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
        | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['109','119'])).

thf('121',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_C )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v5_pre_topc @ X2 @ X1 @ sk_D_1 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( r1_tsep_1 @ X1 @ sk_C )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['108','120'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( r1_tsep_1 @ sk_B @ sk_C )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['107','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ~ ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( r1_tsep_1 @ sk_B @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['106','122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( r1_tsep_1 @ sk_B @ sk_C )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['105','123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['103','124'])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) @ sk_D_1 )
        | ~ ( r4_tsep_1 @ X0 @ sk_B @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['102','126'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['101','127'])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_D_1 )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['49'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('138',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( v2_pre_topc @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('146',plain,
    ( ( l1_pre_topc @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('147',plain,
    ( ( v1_funct_1 @ sk_F )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('148',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['22'])).

thf('149',plain,
    ( ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['111'])).

thf('150',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('151',plain,
    ( ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['104'])).

thf('152',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['31'])).

thf('153',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('154',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['52'])).

thf('155',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('156',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( v1_funct_1 @ ( sk_E @ X32 @ X30 @ X31 ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['156','162'])).

thf('164',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('165',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('166',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X31 @ ( sk_D @ X32 @ X30 @ X31 ) @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X32 @ ( sk_E @ X32 @ X30 @ X31 ) ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['166','172'])).

thf('174',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['165','173'])).

thf('175',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('176',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X31 @ ( sk_D @ X32 @ X30 @ X31 ) @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X32 @ ( sk_E @ X32 @ X30 @ X31 ) ) @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ ( sk_D @ X32 @ X30 @ X31 ) ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['176','182'])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['175','183'])).

thf('185',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('186',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X31 @ ( sk_D @ X32 @ X30 @ X31 ) @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X32 @ ( sk_E @ X32 @ X30 @ X31 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ ( sk_D @ X32 @ X30 @ X31 ) ) ) ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['186','192'])).

thf('194',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['185','193'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 )
      | ( X0 != X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('196',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_funct_2 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['194','196'])).

thf('198',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['184','197'])).

thf('199',plain,
    ( ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['174','199'])).

thf('201',plain,
    ( ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('203',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X31 @ ( sk_D @ X32 @ X30 @ X31 ) @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X30 @ ( sk_E @ X32 @ X30 @ X31 ) ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['206','207','208'])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['203','209'])).

thf('211',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['202','210'])).

thf('212',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('213',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X31 @ ( sk_D @ X32 @ X30 @ X31 ) @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X30 @ ( sk_E @ X32 @ X30 @ X31 ) ) @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ ( sk_D @ X32 @ X30 @ X31 ) ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['213','219'])).

thf('221',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['212','220'])).

thf('222',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('223',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X31 @ ( sk_D @ X32 @ X30 @ X31 ) @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X30 @ ( sk_E @ X32 @ X30 @ X31 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ ( sk_D @ X32 @ X30 @ X31 ) ) ) ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['223','229'])).

thf('231',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['222','230'])).

thf('232',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['165','173'])).

thf('233',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['175','183'])).

thf('234',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['185','193'])).

thf('235',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('236',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('237',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( l1_pre_topc @ ( sk_D @ X32 @ X30 @ X31 ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( l1_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( l1_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['237','243'])).

thf('245',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['236','244'])).

thf('246',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('247',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( v2_pre_topc @ ( sk_D @ X32 @ X30 @ X31 ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v2_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v2_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['247','253'])).

thf('255',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['246','254'])).

thf('256',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('257',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( v1_funct_2 @ ( sk_E @ X32 @ X30 @ X31 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) ) @ ( u1_struct_0 @ ( sk_D @ X32 @ X30 @ X31 ) ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v1_funct_2 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['257','263'])).

thf('265',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['256','264'])).

thf('266',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('267',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( m1_subset_1 @ ( sk_E @ X32 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) ) @ ( u1_struct_0 @ ( sk_D @ X32 @ X30 @ X31 ) ) ) ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['270','271','272'])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['267','273'])).

thf('275',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['266','274'])).

thf(d13_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( l1_pre_topc @ B )
            & ( v2_pre_topc @ B )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( m1_pre_topc @ C @ A )
                & ~ ( v2_struct_0 @ C ) )
             => ! [D: $i] :
                  ( ( ( m1_pre_topc @ D @ A )
                    & ~ ( v2_struct_0 @ D ) )
                 => ! [E: $i] :
                      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( v1_funct_1 @ E ) )
                     => ! [F: $i] :
                          ( ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v1_funct_1 @ F ) )
                         => ( ( ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ ( k3_tmap_1 @ A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) )
                              | ( r1_tsep_1 @ C @ D ) )
                           => ! [G: $i] :
                                ( ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) )
                                  & ( v1_funct_2 @ G @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                                  & ( v1_funct_1 @ G ) )
                               => ( ( G
                                    = ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                <=> ( ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ G ) @ F )
                                    & ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ G ) @ E ) ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ G @ F @ E @ D @ C @ B @ A )
     => ( ( G
          = ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
      <=> ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ G ) @ E )
          & ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ G ) @ F ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r1_tsep_1 @ C @ D )
        | ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ ( k3_tmap_1 @ A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) )
     => ( zip_tseitin_0 @ F @ E @ D @ C @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ( ( zip_tseitin_0 @ F @ E @ D @ C @ B @ A )
                           => ! [G: $i] :
                                ( ( ( v1_funct_1 @ G )
                                  & ( v1_funct_2 @ G @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                                  & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                               => ( zip_tseitin_1 @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) )).

thf('276',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ( zip_tseitin_1 @ X21 @ X20 @ X22 @ X18 @ X23 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X19 @ X23 @ X18 ) ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ ( k1_tsep_1 @ X19 @ X23 @ X18 ) ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( zip_tseitin_0 @ X20 @ X22 @ X18 @ X23 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X19 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('277',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ sk_A )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( m1_pre_topc @ sk_C @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('282',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      | ~ ( r1_tsep_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('283',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( zip_tseitin_0 @ X3 @ X2 @ sk_C @ sk_B @ X1 @ X0 )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['277','278','279','280','283','284'])).

thf('286',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['285'])).

thf('287',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['265','286'])).

thf('288',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['255','288'])).

thf('290',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['289'])).

thf('291',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['245','290'])).

thf('292',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['291'])).

thf('293',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['235','292'])).

thf('294',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['293'])).

thf('295',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['234','294'])).

thf('296',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['295'])).

thf('297',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['233','296'])).

thf('298',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['297'])).

thf('299',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['232','298'])).

thf('300',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['231','300'])).

thf('302',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['221','302'])).

thf('304',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['303'])).

thf('305',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['211','304'])).

thf('306',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['305'])).

thf('307',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['202','210'])).

thf('308',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['212','220'])).

thf('309',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['222','230'])).

thf('310',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_funct_2 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('311',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['308','311'])).

thf('313',plain,
    ( ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['312'])).

thf('314',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['307','313'])).

thf('315',plain,
    ( ( ( r2_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X11 ) @ ( k3_tmap_1 @ X12 @ X11 @ ( k1_tsep_1 @ X12 @ X10 @ X13 ) @ X10 @ X14 ) @ X15 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ ( k3_tmap_1 @ X12 @ X11 @ ( k1_tsep_1 @ X12 @ X10 @ X13 ) @ X13 @ X14 ) @ X16 )
      | ( X14
        = ( k10_tmap_1 @ X12 @ X11 @ X10 @ X13 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X16 @ X15 @ X13 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('317',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ~ ( zip_tseitin_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
        | ( ( sk_E @ sk_C @ sk_B @ sk_A )
          = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
        | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['315','316'])).

thf('318',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['306','317'])).

thf('319',plain,
    ( ( ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['201','319'])).

thf('321',plain,
    ( ( ( ( sk_E @ sk_C @ sk_B @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['202','210'])).

thf('323',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('324',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X31 @ ( sk_D @ X32 @ X30 @ X31 ) @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X30 @ ( sk_E @ X32 @ X30 @ X31 ) ) @ X30 @ ( sk_D @ X32 @ X30 @ X31 ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('327',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['327','328','329'])).

thf('331',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['324','330'])).

thf('332',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['323','331'])).

thf('333',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['212','220'])).

thf('334',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['222','230'])).

thf('335',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['246','254'])).

thf('336',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['236','244'])).

thf('337',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['165','173'])).

thf('338',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('339',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X31 @ ( sk_D @ X32 @ X30 @ X31 ) @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ X32 @ ( sk_E @ X32 @ X30 @ X31 ) ) @ X32 @ ( sk_D @ X32 @ X30 @ X31 ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('342',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['340','341'])).

thf('343',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_B @ sk_A ) ) @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['342','343','344'])).

thf('346',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['339','345'])).

thf('347',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['338','346'])).

thf('348',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['175','183'])).

thf('349',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['185','193'])).

thf('350',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v2_struct_0 @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
      | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
      | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,
    ( ! [X44: $i,X45: $i,X46: $i] :
        ( ( v2_struct_0 @ X44 )
        | ~ ( v2_pre_topc @ X44 )
        | ~ ( l1_pre_topc @ X44 )
        | ~ ( v1_funct_1 @ X45 )
        | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
        | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
        | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
        | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
        | ~ ( v1_funct_1 @ X46 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) )
   <= ! [X44: $i,X45: $i,X46: $i] :
        ( ( v2_struct_0 @ X44 )
        | ~ ( v2_pre_topc @ X44 )
        | ~ ( l1_pre_topc @ X44 )
        | ~ ( v1_funct_1 @ X45 )
        | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
        | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
        | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
        | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
        | ~ ( v1_funct_1 @ X46 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ),
    inference(split,[status(esa)],['350'])).

thf('352',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['349','351'])).

thf('353',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['348','352'])).

thf('354',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['353'])).

thf('355',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['347','354'])).

thf('356',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['355'])).

thf('357',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['337','356'])).

thf('358',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['336','358'])).

thf('360',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['359'])).

thf('361',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['335','360'])).

thf('362',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
        | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['361'])).

thf('363',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['334','362'])).

thf('364',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['363'])).

thf('365',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['333','364'])).

thf('366',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['365'])).

thf('367',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['332','366'])).

thf('368',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['367'])).

thf('369',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['322','368'])).

thf('370',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['369'])).

thf('371',plain,
    ( ( ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup+',[status(thm)],['321','370'])).

thf('372',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['371'])).

thf('373',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['256','264'])).

thf('374',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( m1_subset_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['266','274'])).

thf('375',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ~ ( v1_funct_1 @ ( sk_E @ X32 @ X30 @ X31 ) )
      | ~ ( v1_funct_2 @ ( sk_E @ X32 @ X30 @ X31 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) ) @ ( u1_struct_0 @ ( sk_D @ X32 @ X30 @ X31 ) ) )
      | ~ ( v5_pre_topc @ ( sk_E @ X32 @ X30 @ X31 ) @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) @ ( sk_D @ X32 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ ( sk_E @ X32 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X31 @ X30 @ X32 ) ) @ ( u1_struct_0 @ ( sk_D @ X32 @ X30 @ X31 ) ) ) ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('376',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['374','375'])).

thf('377',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('378',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('380',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('381',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['376','377','378','379','380','381'])).

thf('383',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['382'])).

thf('384',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['373','383'])).

thf('385',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_C @ sk_B @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['384'])).

thf('386',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['372','385'])).

thf('387',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['386'])).

thf('388',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['164','387'])).

thf('389',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['388'])).

thf('390',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( r1_tsep_1 @ X30 @ X32 )
      | ~ ( v2_struct_0 @ ( sk_D @ X32 @ X30 @ X31 ) )
      | ( r3_tsep_1 @ X31 @ X30 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('391',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['389','390'])).

thf('392',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('393',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('394',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('395',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('396',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('397',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(demod,[status(thm)],['391','392','393','394','395','396'])).

thf('398',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['397'])).

thf('399',plain,
    ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('400',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference('sup-',[status(thm)],['398','399'])).

thf('401',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(clc,[status(thm)],['400','401'])).

thf('403',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ) ),
    inference(clc,[status(thm)],['402','403'])).

thf('405',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('406',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ! [X44: $i,X45: $i,X46: $i] :
          ( ( v2_struct_0 @ X44 )
          | ~ ( v2_pre_topc @ X44 )
          | ~ ( l1_pre_topc @ X44 )
          | ~ ( v1_funct_1 @ X45 )
          | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
          | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
          | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
          | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
          | ~ ( v1_funct_1 @ X46 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['404','405'])).

thf('407',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ! [X44: $i,X45: $i,X46: $i] :
        ( ( v2_struct_0 @ X44 )
        | ~ ( v2_pre_topc @ X44 )
        | ~ ( l1_pre_topc @ X44 )
        | ~ ( v1_funct_1 @ X45 )
        | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) )
        | ~ ( v5_pre_topc @ X45 @ sk_C @ X44 )
        | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X44 ) ) ) )
        | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) ) ) )
        | ~ ( v5_pre_topc @ X46 @ sk_B @ X44 )
        | ~ ( v1_funct_2 @ X46 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X44 ) )
        | ~ ( v1_funct_1 @ X46 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X44 ) ) ),
    inference(split,[status(esa)],['350'])).

thf('408',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['33'])).

thf('409',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('410',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('411',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('412',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('413',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('414',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('415',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('416',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('417',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('418',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X25 @ X28 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('419',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['417','418'])).

thf('420',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( l1_pre_topc @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['416','419'])).

thf('421',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( v2_pre_topc @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ~ ( v1_funct_1 @ sk_E_1 ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['415','420'])).

thf('422',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ sk_E_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2 ) ) )
   <= ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['414','421'])).

thf('423',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['413','422'])).

thf('424',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ sk_F )
        | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['412','423'])).

thf('425',plain,
    ( ! [X0: $i] :
        ( ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
        | ~ ( v1_funct_1 @ sk_F )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['411','424'])).

thf('426',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['410','425'])).

thf('427',plain,
    ( ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['409','426'])).

thf('428',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('429',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('431',plain,
    ( ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['427','428','429','430'])).

thf('432',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) ) ),
    inference(split,[status(esa)],['49'])).

thf('433',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['431','432'])).

thf('434',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['52'])).

thf('435',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['433','434'])).

thf('436',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('437',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['435','436'])).

thf('438',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('439',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( v2_struct_0 @ sk_D_1 )
      & ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
      & ( v1_funct_1 @ sk_E_1 )
      & ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      & ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      & ( v1_funct_1 @ sk_F )
      & ( l1_pre_topc @ sk_D_1 )
      & ( v2_pre_topc @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['437','438'])).

thf('440',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('441',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['439','440'])).

thf('442',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['49'])).

thf('443',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','60','93','144','145','146','147','148','149','150','151','152','153','154','406','407','408','441','442'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qjo6hGOr6a
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.28/2.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.28/2.48  % Solved by: fo/fo7.sh
% 2.28/2.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.28/2.48  % done 1785 iterations in 1.979s
% 2.28/2.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.28/2.48  % SZS output start Refutation
% 2.28/2.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.28/2.48  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 2.28/2.48  thf(sk_C_type, type, sk_C: $i).
% 2.28/2.48  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 2.28/2.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.28/2.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 2.28/2.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.28/2.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.28/2.48  thf(sk_B_type, type, sk_B: $i).
% 2.28/2.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.28/2.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $i > $i > $i > $o).
% 2.28/2.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.28/2.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.28/2.48  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 2.28/2.48  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 2.28/2.48  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 2.28/2.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 2.28/2.48  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 2.28/2.48  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 2.28/2.48  thf(sk_F_type, type, sk_F: $i).
% 2.28/2.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.28/2.48  thf(sk_E_1_type, type, sk_E_1: $i).
% 2.28/2.48  thf(r3_tsep_1_type, type, r3_tsep_1: $i > $i > $i > $o).
% 2.28/2.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.28/2.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.28/2.48  thf(sk_A_type, type, sk_A: $i).
% 2.28/2.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.28/2.48  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 2.28/2.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.28/2.48  thf(t150_tmap_1, conjecture,
% 2.28/2.48    (![A:$i]:
% 2.28/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.28/2.48       ( ![B:$i]:
% 2.28/2.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.28/2.48           ( ![C:$i]:
% 2.28/2.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.28/2.48               ( ( r3_tsep_1 @ A @ B @ C ) <=>
% 2.28/2.48                 ( ( r1_tsep_1 @ B @ C ) & 
% 2.28/2.48                   ( ![D:$i]:
% 2.28/2.48                     ( ( ( ~( v2_struct_0 @ D ) ) & ( v2_pre_topc @ D ) & 
% 2.28/2.48                         ( l1_pre_topc @ D ) ) =>
% 2.28/2.48                       ( ![E:$i]:
% 2.28/2.48                         ( ( ( v1_funct_1 @ E ) & 
% 2.28/2.48                             ( v1_funct_2 @
% 2.28/2.48                               E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                             ( v5_pre_topc @ E @ B @ D ) & 
% 2.28/2.48                             ( m1_subset_1 @
% 2.28/2.48                               E @ 
% 2.28/2.48                               ( k1_zfmisc_1 @
% 2.28/2.48                                 ( k2_zfmisc_1 @
% 2.28/2.48                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.28/2.48                           ( ![F:$i]:
% 2.28/2.48                             ( ( ( v1_funct_1 @ F ) & 
% 2.28/2.48                                 ( v1_funct_2 @
% 2.28/2.48                                   F @ ( u1_struct_0 @ C ) @ 
% 2.28/2.48                                   ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                                 ( v5_pre_topc @ F @ C @ D ) & 
% 2.28/2.48                                 ( m1_subset_1 @
% 2.28/2.48                                   F @ 
% 2.28/2.48                                   ( k1_zfmisc_1 @
% 2.28/2.48                                     ( k2_zfmisc_1 @
% 2.28/2.48                                       ( u1_struct_0 @ C ) @ 
% 2.28/2.48                                       ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.28/2.48                               ( ( v1_funct_1 @
% 2.28/2.48                                   ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) ) & 
% 2.28/2.48                                 ( v1_funct_2 @
% 2.28/2.48                                   ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.28/2.48                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.28/2.48                                   ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                                 ( v5_pre_topc @
% 2.28/2.48                                   ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.28/2.48                                   ( k1_tsep_1 @ A @ B @ C ) @ D ) & 
% 2.28/2.48                                 ( m1_subset_1 @
% 2.28/2.48                                   ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.28/2.48                                   ( k1_zfmisc_1 @
% 2.28/2.48                                     ( k2_zfmisc_1 @
% 2.28/2.48                                       ( u1_struct_0 @
% 2.28/2.48                                         ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.28/2.48                                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.28/2.48  thf(zf_stmt_0, negated_conjecture,
% 2.28/2.48    (~( ![A:$i]:
% 2.28/2.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.28/2.48            ( l1_pre_topc @ A ) ) =>
% 2.28/2.48          ( ![B:$i]:
% 2.28/2.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.28/2.48              ( ![C:$i]:
% 2.28/2.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.28/2.48                  ( ( r3_tsep_1 @ A @ B @ C ) <=>
% 2.28/2.48                    ( ( r1_tsep_1 @ B @ C ) & 
% 2.28/2.48                      ( ![D:$i]:
% 2.28/2.48                        ( ( ( ~( v2_struct_0 @ D ) ) & ( v2_pre_topc @ D ) & 
% 2.28/2.48                            ( l1_pre_topc @ D ) ) =>
% 2.28/2.48                          ( ![E:$i]:
% 2.28/2.48                            ( ( ( v1_funct_1 @ E ) & 
% 2.28/2.48                                ( v1_funct_2 @
% 2.28/2.48                                  E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                                ( v5_pre_topc @ E @ B @ D ) & 
% 2.28/2.48                                ( m1_subset_1 @
% 2.28/2.48                                  E @ 
% 2.28/2.48                                  ( k1_zfmisc_1 @
% 2.28/2.48                                    ( k2_zfmisc_1 @
% 2.28/2.48                                      ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.28/2.48                              ( ![F:$i]:
% 2.28/2.48                                ( ( ( v1_funct_1 @ F ) & 
% 2.28/2.48                                    ( v1_funct_2 @
% 2.28/2.48                                      F @ ( u1_struct_0 @ C ) @ 
% 2.28/2.48                                      ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                                    ( v5_pre_topc @ F @ C @ D ) & 
% 2.28/2.48                                    ( m1_subset_1 @
% 2.28/2.48                                      F @ 
% 2.28/2.48                                      ( k1_zfmisc_1 @
% 2.28/2.48                                        ( k2_zfmisc_1 @
% 2.28/2.48                                          ( u1_struct_0 @ C ) @ 
% 2.28/2.48                                          ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.28/2.48                                  ( ( v1_funct_1 @
% 2.28/2.48                                      ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) ) & 
% 2.28/2.48                                    ( v1_funct_2 @
% 2.28/2.48                                      ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.28/2.48                                      ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.28/2.48                                      ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                                    ( v5_pre_topc @
% 2.28/2.48                                      ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.28/2.48                                      ( k1_tsep_1 @ A @ B @ C ) @ D ) & 
% 2.28/2.48                                    ( m1_subset_1 @
% 2.28/2.48                                      ( k10_tmap_1 @ A @ D @ B @ C @ E @ F ) @ 
% 2.28/2.48                                      ( k1_zfmisc_1 @
% 2.28/2.48                                        ( k2_zfmisc_1 @
% 2.28/2.48                                          ( u1_struct_0 @
% 2.28/2.48                                            ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.28/2.48                                          ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.28/2.48    inference('cnf.neg', [status(esa)], [t150_tmap_1])).
% 2.28/2.48  thf('0', plain,
% 2.28/2.48      (((r1_tsep_1 @ sk_B @ sk_C) | (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('1', plain,
% 2.28/2.48      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['0'])).
% 2.28/2.48  thf('2', plain,
% 2.28/2.48      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C))
% 2.28/2.48         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('split', [status(esa)], ['0'])).
% 2.28/2.48  thf(t135_tmap_1, axiom,
% 2.28/2.48    (![A:$i]:
% 2.28/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.28/2.48       ( ![B:$i]:
% 2.28/2.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.28/2.48           ( ![C:$i]:
% 2.28/2.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.28/2.48               ( ( r3_tsep_1 @ A @ B @ C ) <=>
% 2.28/2.48                 ( ( r1_tsep_1 @ B @ C ) & 
% 2.28/2.48                   ( ![D:$i]:
% 2.28/2.48                     ( ( ( ~( v2_struct_0 @ D ) ) & ( v2_pre_topc @ D ) & 
% 2.28/2.48                         ( l1_pre_topc @ D ) ) =>
% 2.28/2.48                       ( ![E:$i]:
% 2.28/2.48                         ( ( ( v1_funct_1 @ E ) & 
% 2.28/2.48                             ( v1_funct_2 @
% 2.28/2.48                               E @ 
% 2.28/2.48                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.28/2.48                               ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                             ( m1_subset_1 @
% 2.28/2.48                               E @ 
% 2.28/2.48                               ( k1_zfmisc_1 @
% 2.28/2.48                                 ( k2_zfmisc_1 @
% 2.28/2.48                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.28/2.48                                   ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.28/2.48                           ( ( ( v1_funct_1 @
% 2.28/2.48                                 ( k3_tmap_1 @
% 2.28/2.48                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) ) & 
% 2.28/2.48                               ( v1_funct_2 @
% 2.28/2.48                                 ( k3_tmap_1 @
% 2.28/2.48                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ 
% 2.28/2.48                                 ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                               ( v5_pre_topc @
% 2.28/2.48                                 ( k3_tmap_1 @
% 2.28/2.48                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ 
% 2.28/2.48                                 B @ D ) & 
% 2.28/2.48                               ( m1_subset_1 @
% 2.28/2.48                                 ( k3_tmap_1 @
% 2.28/2.48                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ B @ E ) @ 
% 2.28/2.48                                 ( k1_zfmisc_1 @
% 2.28/2.48                                   ( k2_zfmisc_1 @
% 2.28/2.48                                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) ) ) ) & 
% 2.28/2.48                               ( v1_funct_1 @
% 2.28/2.48                                 ( k3_tmap_1 @
% 2.28/2.48                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) ) & 
% 2.28/2.48                               ( v1_funct_2 @
% 2.28/2.48                                 ( k3_tmap_1 @
% 2.28/2.48                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ 
% 2.28/2.48                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                               ( v5_pre_topc @
% 2.28/2.48                                 ( k3_tmap_1 @
% 2.28/2.48                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ 
% 2.28/2.48                                 C @ D ) & 
% 2.28/2.48                               ( m1_subset_1 @
% 2.28/2.48                                 ( k3_tmap_1 @
% 2.28/2.48                                   A @ D @ ( k1_tsep_1 @ A @ B @ C ) @ C @ E ) @ 
% 2.28/2.48                                 ( k1_zfmisc_1 @
% 2.28/2.48                                   ( k2_zfmisc_1 @
% 2.28/2.48                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 2.28/2.48                             ( ( v1_funct_1 @ E ) & 
% 2.28/2.48                               ( v1_funct_2 @
% 2.28/2.48                                 E @ 
% 2.28/2.48                                 ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.28/2.48                                 ( u1_struct_0 @ D ) ) & 
% 2.28/2.48                               ( v5_pre_topc @
% 2.28/2.48                                 E @ ( k1_tsep_1 @ A @ B @ C ) @ D ) & 
% 2.28/2.48                               ( m1_subset_1 @
% 2.28/2.48                                 E @ 
% 2.28/2.48                                 ( k1_zfmisc_1 @
% 2.28/2.48                                   ( k2_zfmisc_1 @
% 2.28/2.48                                     ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) @ 
% 2.28/2.48                                     ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.28/2.48  thf('3', plain,
% 2.28/2.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.48         ((v2_struct_0 @ X30)
% 2.28/2.48          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.48          | ~ (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.48          | (r1_tsep_1 @ X30 @ X32)
% 2.28/2.48          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.48          | (v2_struct_0 @ X32)
% 2.28/2.48          | ~ (l1_pre_topc @ X31)
% 2.28/2.48          | ~ (v2_pre_topc @ X31)
% 2.28/2.48          | (v2_struct_0 @ X31))),
% 2.28/2.48      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.48  thf('4', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A)
% 2.28/2.48         | ~ (v2_pre_topc @ sk_A)
% 2.28/2.48         | ~ (l1_pre_topc @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.28/2.48         | (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['2', '3'])).
% 2.28/2.48  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('9', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 2.28/2.48  thf('10', plain,
% 2.28/2.48      (((v1_funct_1 @ sk_E_1)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('11', plain,
% 2.28/2.48      ((~ (r1_tsep_1 @ sk_B @ sk_C)) <= (~ ((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('split', [status(esa)], ['10'])).
% 2.28/2.48  thf('12', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 2.28/2.48         <= (~ ((r1_tsep_1 @ sk_B @ sk_C)) & ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['9', '11'])).
% 2.28/2.48  thf('13', plain, (~ (v2_struct_0 @ sk_B)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('14', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 2.28/2.48         <= (~ ((r1_tsep_1 @ sk_B @ sk_C)) & ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('clc', [status(thm)], ['12', '13'])).
% 2.28/2.48  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('16', plain,
% 2.28/2.48      (((v2_struct_0 @ sk_C))
% 2.28/2.48         <= (~ ((r1_tsep_1 @ sk_B @ sk_C)) & ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('clc', [status(thm)], ['14', '15'])).
% 2.28/2.48  thf('17', plain, (~ (v2_struct_0 @ sk_C)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('18', plain,
% 2.28/2.48      (((r1_tsep_1 @ sk_B @ sk_C)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('sup-', [status(thm)], ['16', '17'])).
% 2.28/2.48  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('20', plain,
% 2.28/2.48      (((v1_funct_1 @ sk_F)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('21', plain, (((v1_funct_1 @ sk_F)) <= (((v1_funct_1 @ sk_F)))),
% 2.28/2.48      inference('split', [status(esa)], ['20'])).
% 2.28/2.48  thf('22', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('23', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.48      inference('split', [status(esa)], ['22'])).
% 2.28/2.48  thf('24', plain,
% 2.28/2.48      (((m1_subset_1 @ sk_F @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('25', plain,
% 2.28/2.48      (((m1_subset_1 @ sk_F @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))))
% 2.28/2.48         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('split', [status(esa)], ['24'])).
% 2.28/2.48  thf('26', plain,
% 2.28/2.48      (((l1_pre_topc @ sk_D_1)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('27', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['26'])).
% 2.28/2.48  thf('28', plain,
% 2.28/2.48      (((v2_pre_topc @ sk_D_1)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('29', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['28'])).
% 2.28/2.48  thf('30', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['10'])).
% 2.28/2.48  thf('31', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('32', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.48      inference('split', [status(esa)], ['31'])).
% 2.28/2.48  thf('33', plain,
% 2.28/2.48      (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('34', plain,
% 2.28/2.48      (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))))
% 2.28/2.48         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('split', [status(esa)], ['33'])).
% 2.28/2.48  thf(dt_k10_tmap_1, axiom,
% 2.28/2.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.28/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.28/2.48         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 2.28/2.48         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 2.28/2.48         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 2.28/2.48         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 2.28/2.48         ( v1_funct_1 @ E ) & 
% 2.28/2.48         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.28/2.48         ( m1_subset_1 @
% 2.28/2.48           E @ 
% 2.28/2.48           ( k1_zfmisc_1 @
% 2.28/2.48             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 2.28/2.48         ( v1_funct_1 @ F ) & 
% 2.28/2.48         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 2.28/2.48         ( m1_subset_1 @
% 2.28/2.48           F @ 
% 2.28/2.48           ( k1_zfmisc_1 @
% 2.28/2.48             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.28/2.48       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.28/2.48         ( v1_funct_2 @
% 2.28/2.48           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.28/2.48           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 2.28/2.48         ( m1_subset_1 @
% 2.28/2.48           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.28/2.48           ( k1_zfmisc_1 @
% 2.28/2.48             ( k2_zfmisc_1 @
% 2.28/2.48               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.28/2.48               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.28/2.48  thf('35', plain,
% 2.28/2.48      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.28/2.48         (~ (m1_subset_1 @ X24 @ 
% 2.28/2.48             (k1_zfmisc_1 @ 
% 2.28/2.48              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))))
% 2.28/2.48          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 2.28/2.48          | ~ (v1_funct_1 @ X24)
% 2.28/2.48          | ~ (m1_pre_topc @ X27 @ X28)
% 2.28/2.48          | (v2_struct_0 @ X27)
% 2.28/2.48          | ~ (m1_pre_topc @ X25 @ X28)
% 2.28/2.48          | (v2_struct_0 @ X25)
% 2.28/2.48          | ~ (l1_pre_topc @ X26)
% 2.28/2.48          | ~ (v2_pre_topc @ X26)
% 2.28/2.48          | (v2_struct_0 @ X26)
% 2.28/2.48          | ~ (l1_pre_topc @ X28)
% 2.28/2.48          | ~ (v2_pre_topc @ X28)
% 2.28/2.48          | (v2_struct_0 @ X28)
% 2.28/2.48          | ~ (v1_funct_1 @ X29)
% 2.28/2.48          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 2.28/2.48          | ~ (m1_subset_1 @ X29 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 2.28/2.48          | (v1_funct_2 @ (k10_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29) @ 
% 2.28/2.48             (u1_struct_0 @ (k1_tsep_1 @ X28 @ X25 @ X27)) @ 
% 2.28/2.48             (u1_struct_0 @ X26)))),
% 2.28/2.48      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 2.28/2.48  thf('36', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((v1_funct_2 @ 
% 2.28/2.48            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.28/2.48            (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.28/2.48            (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (v2_pre_topc @ X1)
% 2.28/2.48           | ~ (l1_pre_topc @ X1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (m1_pre_topc @ X0 @ X1)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_E_1)
% 2.28/2.48           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))))
% 2.28/2.48         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('sup-', [status(thm)], ['34', '35'])).
% 2.28/2.48  thf('37', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          (~ (v1_funct_1 @ sk_E_1)
% 2.28/2.48           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | (v1_funct_2 @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2) @ 
% 2.28/2.48              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ X1)) @ 
% 2.28/2.48              (u1_struct_0 @ sk_D_1))))
% 2.28/2.48         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('sup-', [status(thm)], ['32', '36'])).
% 2.28/2.48  thf('38', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((v1_funct_2 @ 
% 2.28/2.48            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.28/2.48            (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.28/2.48            (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (v2_pre_topc @ X1)
% 2.28/2.48           | ~ (l1_pre_topc @ X1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('sup-', [status(thm)], ['30', '37'])).
% 2.28/2.48  thf('39', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          (~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | (v1_funct_2 @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2) @ 
% 2.28/2.48              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ X1)) @ 
% 2.28/2.48              (u1_struct_0 @ sk_D_1))))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['29', '38'])).
% 2.28/2.48  thf('40', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((v1_funct_2 @ 
% 2.28/2.48            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.28/2.48            (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.28/2.48            (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (v2_pre_topc @ X1)
% 2.28/2.48           | ~ (l1_pre_topc @ X1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['27', '39'])).
% 2.28/2.48  thf('41', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          (~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_F)
% 2.28/2.48           | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | (v1_funct_2 @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.28/2.48              (u1_struct_0 @ sk_D_1))))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['25', '40'])).
% 2.28/2.48  thf('42', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          ((v1_funct_2 @ 
% 2.28/2.48            (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48            (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.28/2.48            (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ sk_F)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['23', '41'])).
% 2.28/2.48  thf('43', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          (~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | (v1_funct_2 @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.28/2.48              (u1_struct_0 @ sk_D_1))))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['21', '42'])).
% 2.28/2.48  thf('44', plain,
% 2.28/2.48      ((((v1_funct_2 @ 
% 2.28/2.48          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48          (u1_struct_0 @ sk_D_1))
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | ~ (v2_pre_topc @ sk_A)
% 2.28/2.48         | ~ (l1_pre_topc @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_B)
% 2.28/2.48         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['19', '43'])).
% 2.28/2.48  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('48', plain,
% 2.28/2.48      ((((v1_funct_2 @ 
% 2.28/2.48          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48          (u1_struct_0 @ sk_D_1))
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_B)
% 2.28/2.48         | (v2_struct_0 @ sk_C)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 2.28/2.48  thf('49', plain,
% 2.28/2.48      ((~ (m1_subset_1 @ 
% 2.28/2.48           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48           (k1_zfmisc_1 @ 
% 2.28/2.48            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48             (u1_struct_0 @ sk_D_1))))
% 2.28/2.48        | ~ (v5_pre_topc @ 
% 2.28/2.48             (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48        | ~ (v1_funct_2 @ 
% 2.28/2.48             (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48             (u1_struct_0 @ sk_D_1))
% 2.28/2.48        | ~ (v1_funct_1 @ 
% 2.28/2.48             (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('50', plain,
% 2.28/2.48      ((~ (v1_funct_2 @ 
% 2.28/2.48           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48           (u1_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (~
% 2.28/2.48             ((v1_funct_2 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.48      inference('split', [status(esa)], ['49'])).
% 2.28/2.48  thf('51', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B)
% 2.28/2.48         | (v2_struct_0 @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_A)))
% 2.28/2.48         <= (~
% 2.28/2.48             ((v1_funct_2 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['48', '50'])).
% 2.28/2.48  thf('52', plain,
% 2.28/2.48      ((~ (v2_struct_0 @ sk_D_1)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('53', plain,
% 2.28/2.48      ((~ (v2_struct_0 @ sk_D_1)) <= (~ ((v2_struct_0 @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['52'])).
% 2.28/2.48  thf('54', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 2.28/2.48         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.48             ~
% 2.28/2.48             ((v1_funct_2 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['51', '53'])).
% 2.28/2.48  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('56', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 2.28/2.48         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.48             ~
% 2.28/2.48             ((v1_funct_2 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('clc', [status(thm)], ['54', '55'])).
% 2.28/2.48  thf('57', plain, (~ (v2_struct_0 @ sk_C)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('58', plain,
% 2.28/2.48      (((v2_struct_0 @ sk_B))
% 2.28/2.48         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.48             ~
% 2.28/2.48             ((v1_funct_2 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('clc', [status(thm)], ['56', '57'])).
% 2.28/2.48  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('60', plain,
% 2.28/2.48      (((v1_funct_2 @ 
% 2.28/2.48         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48         (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.48       ~ ((v1_funct_1 @ sk_E_1)) | ~ ((v2_pre_topc @ sk_D_1)) | 
% 2.28/2.48       ~ ((l1_pre_topc @ sk_D_1)) | ~ ((v1_funct_1 @ sk_F)) | 
% 2.28/2.48       ~ ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.48       ~
% 2.28/2.48       ((m1_subset_1 @ sk_F @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.48       ~
% 2.28/2.48       ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.48       ~
% 2.28/2.48       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.48       ((v2_struct_0 @ sk_D_1))),
% 2.28/2.48      inference('sup-', [status(thm)], ['58', '59'])).
% 2.28/2.48  thf('61', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('62', plain, (((v1_funct_1 @ sk_F)) <= (((v1_funct_1 @ sk_F)))),
% 2.28/2.48      inference('split', [status(esa)], ['20'])).
% 2.28/2.48  thf('63', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.48      inference('split', [status(esa)], ['22'])).
% 2.28/2.48  thf('64', plain,
% 2.28/2.48      (((m1_subset_1 @ sk_F @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))))
% 2.28/2.48         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('split', [status(esa)], ['24'])).
% 2.28/2.48  thf('65', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['26'])).
% 2.28/2.48  thf('66', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['28'])).
% 2.28/2.48  thf('67', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['10'])).
% 2.28/2.48  thf('68', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.48      inference('split', [status(esa)], ['31'])).
% 2.28/2.48  thf('69', plain,
% 2.28/2.48      (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))))
% 2.28/2.48         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('split', [status(esa)], ['33'])).
% 2.28/2.48  thf('70', plain,
% 2.28/2.48      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.28/2.48         (~ (m1_subset_1 @ X24 @ 
% 2.28/2.48             (k1_zfmisc_1 @ 
% 2.28/2.48              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))))
% 2.28/2.48          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 2.28/2.48          | ~ (v1_funct_1 @ X24)
% 2.28/2.48          | ~ (m1_pre_topc @ X27 @ X28)
% 2.28/2.48          | (v2_struct_0 @ X27)
% 2.28/2.48          | ~ (m1_pre_topc @ X25 @ X28)
% 2.28/2.48          | (v2_struct_0 @ X25)
% 2.28/2.48          | ~ (l1_pre_topc @ X26)
% 2.28/2.48          | ~ (v2_pre_topc @ X26)
% 2.28/2.48          | (v2_struct_0 @ X26)
% 2.28/2.48          | ~ (l1_pre_topc @ X28)
% 2.28/2.48          | ~ (v2_pre_topc @ X28)
% 2.28/2.48          | (v2_struct_0 @ X28)
% 2.28/2.48          | ~ (v1_funct_1 @ X29)
% 2.28/2.48          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 2.28/2.48          | ~ (m1_subset_1 @ X29 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 2.28/2.48          | (m1_subset_1 @ (k10_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29) @ 
% 2.28/2.48             (k1_zfmisc_1 @ 
% 2.28/2.48              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X28 @ X25 @ X27)) @ 
% 2.28/2.48               (u1_struct_0 @ X26)))))),
% 2.28/2.48      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 2.28/2.48  thf('71', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((m1_subset_1 @ 
% 2.28/2.48            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.28/2.48            (k1_zfmisc_1 @ 
% 2.28/2.48             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.28/2.48              (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (v2_pre_topc @ X1)
% 2.28/2.48           | ~ (l1_pre_topc @ X1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (m1_pre_topc @ X0 @ X1)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_E_1)
% 2.28/2.48           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))))
% 2.28/2.48         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('sup-', [status(thm)], ['69', '70'])).
% 2.28/2.48  thf('72', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          (~ (v1_funct_1 @ sk_E_1)
% 2.28/2.48           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | (m1_subset_1 @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2) @ 
% 2.28/2.48              (k1_zfmisc_1 @ 
% 2.28/2.48               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ X1)) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))))))
% 2.28/2.48         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('sup-', [status(thm)], ['68', '71'])).
% 2.28/2.48  thf('73', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((m1_subset_1 @ 
% 2.28/2.48            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.28/2.48            (k1_zfmisc_1 @ 
% 2.28/2.48             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.28/2.48              (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (v2_pre_topc @ X1)
% 2.28/2.48           | ~ (l1_pre_topc @ X1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('sup-', [status(thm)], ['67', '72'])).
% 2.28/2.48  thf('74', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          (~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | (m1_subset_1 @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2) @ 
% 2.28/2.48              (k1_zfmisc_1 @ 
% 2.28/2.48               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ X1)) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))))))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['66', '73'])).
% 2.28/2.48  thf('75', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((m1_subset_1 @ 
% 2.28/2.48            (k10_tmap_1 @ X1 @ sk_D_1 @ sk_B @ X0 @ sk_E_1 @ X2) @ 
% 2.28/2.48            (k1_zfmisc_1 @ 
% 2.28/2.48             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_B @ X0)) @ 
% 2.28/2.48              (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (v2_pre_topc @ X1)
% 2.28/2.48           | ~ (l1_pre_topc @ X1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X1)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (m1_pre_topc @ X0 @ X1)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['65', '74'])).
% 2.28/2.48  thf('76', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          (~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_F)
% 2.28/2.48           | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | (m1_subset_1 @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (k1_zfmisc_1 @ 
% 2.28/2.48               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))))))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['64', '75'])).
% 2.28/2.48  thf('77', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          ((m1_subset_1 @ 
% 2.28/2.48            (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48            (k1_zfmisc_1 @ 
% 2.28/2.48             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.28/2.48              (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v1_funct_1 @ sk_F)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['63', '76'])).
% 2.28/2.48  thf('78', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          (~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)
% 2.28/2.48           | (m1_subset_1 @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (k1_zfmisc_1 @ 
% 2.28/2.48               (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_B @ sk_C)) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))))))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['62', '77'])).
% 2.28/2.48  thf('79', plain,
% 2.28/2.48      ((((m1_subset_1 @ 
% 2.28/2.48          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48          (k1_zfmisc_1 @ 
% 2.28/2.48           (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48            (u1_struct_0 @ sk_D_1))))
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | ~ (v2_pre_topc @ sk_A)
% 2.28/2.48         | ~ (l1_pre_topc @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_B)
% 2.28/2.48         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['61', '78'])).
% 2.28/2.48  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('82', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('83', plain,
% 2.28/2.48      ((((m1_subset_1 @ 
% 2.28/2.48          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48          (k1_zfmisc_1 @ 
% 2.28/2.48           (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48            (u1_struct_0 @ sk_D_1))))
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_B)
% 2.28/2.48         | (v2_struct_0 @ sk_C)))
% 2.28/2.48         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 2.28/2.48  thf('84', plain,
% 2.28/2.48      ((~ (m1_subset_1 @ 
% 2.28/2.48           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48           (k1_zfmisc_1 @ 
% 2.28/2.48            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48             (u1_struct_0 @ sk_D_1)))))
% 2.28/2.48         <= (~
% 2.28/2.48             ((m1_subset_1 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ 
% 2.28/2.48                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48                 (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('split', [status(esa)], ['49'])).
% 2.28/2.48  thf('85', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B)
% 2.28/2.48         | (v2_struct_0 @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_A)))
% 2.28/2.48         <= (~
% 2.28/2.48             ((m1_subset_1 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ 
% 2.28/2.48                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48                 (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['83', '84'])).
% 2.28/2.48  thf('86', plain,
% 2.28/2.48      ((~ (v2_struct_0 @ sk_D_1)) <= (~ ((v2_struct_0 @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['52'])).
% 2.28/2.48  thf('87', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 2.28/2.48         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.48             ~
% 2.28/2.48             ((m1_subset_1 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ 
% 2.28/2.48                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48                 (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['85', '86'])).
% 2.28/2.48  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('89', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 2.28/2.48         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.48             ~
% 2.28/2.48             ((m1_subset_1 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ 
% 2.28/2.48                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48                 (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('clc', [status(thm)], ['87', '88'])).
% 2.28/2.48  thf('90', plain, (~ (v2_struct_0 @ sk_C)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('91', plain,
% 2.28/2.48      (((v2_struct_0 @ sk_B))
% 2.28/2.48         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.48             ~
% 2.28/2.48             ((m1_subset_1 @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ 
% 2.28/2.48                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48                 (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('clc', [status(thm)], ['89', '90'])).
% 2.28/2.48  thf('92', plain, (~ (v2_struct_0 @ sk_B)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('93', plain,
% 2.28/2.48      (((m1_subset_1 @ 
% 2.28/2.48         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.48           (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.48       ~ ((v1_funct_1 @ sk_E_1)) | ~ ((v2_pre_topc @ sk_D_1)) | 
% 2.28/2.48       ~ ((l1_pre_topc @ sk_D_1)) | ~ ((v1_funct_1 @ sk_F)) | 
% 2.28/2.48       ~ ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.48       ~
% 2.28/2.48       ((m1_subset_1 @ sk_F @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.48       ~
% 2.28/2.48       ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.48       ~
% 2.28/2.48       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.48       ((v2_struct_0 @ sk_D_1))),
% 2.28/2.48      inference('sup-', [status(thm)], ['91', '92'])).
% 2.28/2.48  thf('94', plain,
% 2.28/2.48      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C))
% 2.28/2.48         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('split', [status(esa)], ['0'])).
% 2.28/2.48  thf(t85_tsep_1, axiom,
% 2.28/2.48    (![A:$i]:
% 2.28/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.28/2.48       ( ![B:$i]:
% 2.28/2.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 2.28/2.48           ( ![C:$i]:
% 2.28/2.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.28/2.48               ( ( ( r1_tsep_1 @ B @ C ) & ( r4_tsep_1 @ A @ B @ C ) ) <=>
% 2.28/2.48                 ( r3_tsep_1 @ A @ B @ C ) ) ) ) ) ) ))).
% 2.28/2.48  thf('95', plain,
% 2.28/2.48      (![X41 : $i, X42 : $i, X43 : $i]:
% 2.28/2.48         ((v2_struct_0 @ X41)
% 2.28/2.48          | ~ (m1_pre_topc @ X41 @ X42)
% 2.28/2.48          | ~ (r3_tsep_1 @ X42 @ X41 @ X43)
% 2.28/2.48          | (r4_tsep_1 @ X42 @ X41 @ X43)
% 2.28/2.48          | ~ (m1_pre_topc @ X43 @ X42)
% 2.28/2.48          | (v2_struct_0 @ X43)
% 2.28/2.48          | ~ (l1_pre_topc @ X42)
% 2.28/2.48          | ~ (v2_pre_topc @ X42)
% 2.28/2.48          | (v2_struct_0 @ X42))),
% 2.28/2.48      inference('cnf', [status(esa)], [t85_tsep_1])).
% 2.28/2.48  thf('96', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A)
% 2.28/2.48         | ~ (v2_pre_topc @ sk_A)
% 2.28/2.48         | ~ (l1_pre_topc @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.28/2.48         | (r4_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['94', '95'])).
% 2.28/2.48  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('99', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('100', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('101', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r4_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 2.28/2.48  thf('102', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['10'])).
% 2.28/2.48  thf('103', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.48      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 2.28/2.48  thf('104', plain,
% 2.28/2.48      (((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('105', plain,
% 2.28/2.48      (((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1))
% 2.28/2.48         <= (((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['104'])).
% 2.28/2.48  thf('106', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.48      inference('split', [status(esa)], ['31'])).
% 2.28/2.48  thf('107', plain,
% 2.28/2.48      (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))))
% 2.28/2.48         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('split', [status(esa)], ['33'])).
% 2.28/2.48  thf('108', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['26'])).
% 2.28/2.48  thf('109', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['28'])).
% 2.28/2.48  thf('110', plain, (((v1_funct_1 @ sk_F)) <= (((v1_funct_1 @ sk_F)))),
% 2.28/2.48      inference('split', [status(esa)], ['20'])).
% 2.28/2.48  thf('111', plain,
% 2.28/2.48      (((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | ~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('112', plain,
% 2.28/2.48      (((v5_pre_topc @ sk_F @ sk_C @ sk_D_1))
% 2.28/2.48         <= (((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['111'])).
% 2.28/2.48  thf('113', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.48      inference('split', [status(esa)], ['22'])).
% 2.28/2.48  thf('114', plain,
% 2.28/2.48      (((m1_subset_1 @ sk_F @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))))
% 2.28/2.48         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('split', [status(esa)], ['24'])).
% 2.28/2.48  thf(t145_tmap_1, axiom,
% 2.28/2.48    (![A:$i]:
% 2.28/2.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.28/2.48       ( ![B:$i]:
% 2.28/2.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.28/2.48             ( l1_pre_topc @ B ) ) =>
% 2.28/2.48           ( ![C:$i]:
% 2.28/2.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.28/2.48               ( ![D:$i]:
% 2.28/2.48                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 2.28/2.48                   ( ( r1_tsep_1 @ C @ D ) =>
% 2.28/2.48                     ( ![E:$i]:
% 2.28/2.48                       ( ( ( v1_funct_1 @ E ) & 
% 2.28/2.48                           ( v1_funct_2 @
% 2.28/2.48                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.28/2.48                           ( v5_pre_topc @ E @ C @ B ) & 
% 2.28/2.48                           ( m1_subset_1 @
% 2.28/2.48                             E @ 
% 2.28/2.48                             ( k1_zfmisc_1 @
% 2.28/2.48                               ( k2_zfmisc_1 @
% 2.28/2.48                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.28/2.48                         ( ![F:$i]:
% 2.28/2.48                           ( ( ( v1_funct_1 @ F ) & 
% 2.28/2.48                               ( v1_funct_2 @
% 2.28/2.48                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 2.28/2.48                               ( v5_pre_topc @ F @ D @ B ) & 
% 2.28/2.48                               ( m1_subset_1 @
% 2.28/2.48                                 F @ 
% 2.28/2.48                                 ( k1_zfmisc_1 @
% 2.28/2.48                                   ( k2_zfmisc_1 @
% 2.28/2.48                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.28/2.48                             ( ( r4_tsep_1 @ A @ C @ D ) =>
% 2.28/2.48                               ( ( v1_funct_1 @
% 2.28/2.48                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.28/2.48                                 ( v1_funct_2 @
% 2.28/2.48                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.28/2.48                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.28/2.48                                   ( u1_struct_0 @ B ) ) & 
% 2.28/2.48                                 ( v5_pre_topc @
% 2.28/2.48                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.28/2.48                                   ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 2.28/2.48                                 ( m1_subset_1 @
% 2.28/2.48                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.28/2.48                                   ( k1_zfmisc_1 @
% 2.28/2.48                                     ( k2_zfmisc_1 @
% 2.28/2.48                                       ( u1_struct_0 @
% 2.28/2.48                                         ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.28/2.48                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.28/2.48  thf('115', plain,
% 2.28/2.48      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.28/2.48         ((v2_struct_0 @ X35)
% 2.28/2.48          | ~ (v2_pre_topc @ X35)
% 2.28/2.48          | ~ (l1_pre_topc @ X35)
% 2.28/2.48          | (v2_struct_0 @ X36)
% 2.28/2.48          | ~ (m1_pre_topc @ X36 @ X37)
% 2.28/2.48          | ~ (v1_funct_1 @ X38)
% 2.28/2.48          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X35))
% 2.28/2.48          | ~ (v5_pre_topc @ X38 @ X36 @ X35)
% 2.28/2.48          | ~ (m1_subset_1 @ X38 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X35))))
% 2.28/2.48          | (v5_pre_topc @ (k10_tmap_1 @ X37 @ X35 @ X39 @ X36 @ X40 @ X38) @ 
% 2.28/2.48             (k1_tsep_1 @ X37 @ X39 @ X36) @ X35)
% 2.28/2.48          | ~ (r4_tsep_1 @ X37 @ X39 @ X36)
% 2.28/2.48          | ~ (m1_subset_1 @ X40 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X35))))
% 2.28/2.48          | ~ (v5_pre_topc @ X40 @ X39 @ X35)
% 2.28/2.48          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X35))
% 2.28/2.48          | ~ (v1_funct_1 @ X40)
% 2.28/2.48          | ~ (r1_tsep_1 @ X39 @ X36)
% 2.28/2.48          | ~ (m1_pre_topc @ X39 @ X37)
% 2.28/2.48          | (v2_struct_0 @ X39)
% 2.28/2.48          | ~ (l1_pre_topc @ X37)
% 2.28/2.48          | ~ (v2_pre_topc @ X37)
% 2.28/2.48          | (v2_struct_0 @ X37))),
% 2.28/2.48      inference('cnf', [status(esa)], [t145_tmap_1])).
% 2.28/2.48  thf('116', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (v5_pre_topc @ sk_F @ sk_C @ sk_D_1)
% 2.28/2.48           | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ sk_F)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.48      inference('sup-', [status(thm)], ['114', '115'])).
% 2.28/2.48  thf('117', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_F)
% 2.28/2.48           | ~ (v5_pre_topc @ sk_F @ sk_C @ sk_D_1)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)))
% 2.28/2.48         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.48      inference('sup-', [status(thm)], ['113', '116'])).
% 2.28/2.48  thf('118', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_F)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.48      inference('sup-', [status(thm)], ['112', '117'])).
% 2.28/2.48  thf('119', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)))
% 2.28/2.48         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['110', '118'])).
% 2.28/2.48  thf('120', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['109', '119'])).
% 2.28/2.48  thf('121', plain,
% 2.28/2.48      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.48          ((v2_struct_0 @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ X1 @ sk_C @ X2 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ X1 @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ X1 @ sk_C)
% 2.28/2.48           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.48                (k1_zfmisc_1 @ 
% 2.28/2.48                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.48           | ~ (v5_pre_topc @ X2 @ X1 @ sk_D_1)
% 2.28/2.48           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v1_funct_1 @ X2)
% 2.28/2.48           | ~ (r1_tsep_1 @ X1 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.48           | (v2_struct_0 @ X1)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)))
% 2.28/2.48         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['108', '120'])).
% 2.28/2.48  thf('122', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          ((v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_E_1)
% 2.28/2.48           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48                (u1_struct_0 @ sk_D_1))
% 2.28/2.48           | ~ (v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['107', '121'])).
% 2.28/2.48  thf('123', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          ((v2_struct_0 @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.28/2.48           | ~ (v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_E_1)
% 2.28/2.48           | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)))
% 2.28/2.48         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['106', '122'])).
% 2.28/2.48  thf('124', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          ((v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_E_1)
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['105', '123'])).
% 2.28/2.48  thf('125', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          ((v2_struct_0 @ sk_B)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | (v2_struct_0 @ sk_A)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_E_1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_B)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)))
% 2.28/2.48         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['103', '124'])).
% 2.28/2.48  thf('126', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          ((v2_struct_0 @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | ~ (v1_funct_1 @ sk_E_1)
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | (v2_struct_0 @ sk_A)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | (v2_struct_0 @ sk_B)))
% 2.28/2.48         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('simplify', [status(thm)], ['125'])).
% 2.28/2.48  thf('127', plain,
% 2.28/2.48      ((![X0 : $i]:
% 2.28/2.48          ((v2_struct_0 @ sk_B)
% 2.28/2.48           | (v2_struct_0 @ sk_C)
% 2.28/2.48           | (v2_struct_0 @ sk_A)
% 2.28/2.48           | (v2_struct_0 @ sk_D_1)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.48           | (v5_pre_topc @ 
% 2.28/2.48              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48              (k1_tsep_1 @ X0 @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48           | ~ (r4_tsep_1 @ X0 @ sk_B @ sk_C)
% 2.28/2.48           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.48           | ~ (l1_pre_topc @ X0)
% 2.28/2.48           | ~ (v2_pre_topc @ X0)
% 2.28/2.48           | (v2_struct_0 @ X0)))
% 2.28/2.48         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['102', '126'])).
% 2.28/2.48  thf('128', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_B)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | ~ (v2_pre_topc @ sk_A)
% 2.28/2.48         | ~ (l1_pre_topc @ sk_A)
% 2.28/2.48         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.28/2.48         | (v5_pre_topc @ 
% 2.28/2.48            (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B)))
% 2.28/2.48         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['101', '127'])).
% 2.28/2.48  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('131', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('132', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('133', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_B)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v5_pre_topc @ 
% 2.28/2.48            (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B)))
% 2.28/2.48         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 2.28/2.48  thf('134', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_D_1)
% 2.28/2.48         | (v5_pre_topc @ 
% 2.28/2.48            (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B)))
% 2.28/2.48         <= (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('simplify', [status(thm)], ['133'])).
% 2.28/2.48  thf('135', plain,
% 2.28/2.48      ((~ (v5_pre_topc @ 
% 2.28/2.48           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48           (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))
% 2.28/2.48         <= (~
% 2.28/2.48             ((v5_pre_topc @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['49'])).
% 2.28/2.48  thf('136', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_B)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_D_1)))
% 2.28/2.48         <= (~
% 2.28/2.48             ((v5_pre_topc @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) & 
% 2.28/2.48             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['134', '135'])).
% 2.28/2.48  thf('137', plain,
% 2.28/2.48      ((~ (v2_struct_0 @ sk_D_1)) <= (~ ((v2_struct_0 @ sk_D_1)))),
% 2.28/2.48      inference('split', [status(esa)], ['52'])).
% 2.28/2.48  thf('138', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 2.28/2.48         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.48             ~
% 2.28/2.48             ((v5_pre_topc @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) & 
% 2.28/2.48             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['136', '137'])).
% 2.28/2.48  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('140', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 2.28/2.48         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.48             ~
% 2.28/2.48             ((v5_pre_topc @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) & 
% 2.28/2.48             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('clc', [status(thm)], ['138', '139'])).
% 2.28/2.48  thf('141', plain, (~ (v2_struct_0 @ sk_B)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('142', plain,
% 2.28/2.48      (((v2_struct_0 @ sk_C))
% 2.28/2.48         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.48             ~
% 2.28/2.48             ((v5_pre_topc @ 
% 2.28/2.48               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) & 
% 2.28/2.48             ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.48             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) & 
% 2.28/2.48             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((m1_subset_1 @ sk_F @ 
% 2.28/2.48               (k1_zfmisc_1 @ 
% 2.28/2.48                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.48             ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) & 
% 2.28/2.48             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.48             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.48             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.48             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.48      inference('clc', [status(thm)], ['140', '141'])).
% 2.28/2.48  thf('143', plain, (~ (v2_struct_0 @ sk_C)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('144', plain,
% 2.28/2.48      (((v5_pre_topc @ 
% 2.28/2.48         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.48         (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1)) | 
% 2.28/2.48       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((v2_pre_topc @ sk_D_1)) | 
% 2.28/2.48       ~ ((l1_pre_topc @ sk_D_1)) | ~ ((v1_funct_1 @ sk_F)) | 
% 2.28/2.48       ~ ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.48       ~ ((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) | 
% 2.28/2.48       ~
% 2.28/2.48       ((m1_subset_1 @ sk_F @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.48       ~
% 2.28/2.48       ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.48       ~ ((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) | 
% 2.28/2.48       ~
% 2.28/2.48       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.48       ~ ((v1_funct_1 @ sk_E_1)) | ((v2_struct_0 @ sk_D_1))),
% 2.28/2.48      inference('sup-', [status(thm)], ['142', '143'])).
% 2.28/2.48  thf('145', plain,
% 2.28/2.48      (((v2_pre_topc @ sk_D_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.28/2.48       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['28'])).
% 2.28/2.48  thf('146', plain,
% 2.28/2.48      (((l1_pre_topc @ sk_D_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.28/2.48       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['26'])).
% 2.28/2.48  thf('147', plain,
% 2.28/2.48      (((v1_funct_1 @ sk_F)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.28/2.48       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['20'])).
% 2.28/2.48  thf('148', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.48       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['22'])).
% 2.28/2.48  thf('149', plain,
% 2.28/2.48      (((v5_pre_topc @ sk_F @ sk_C @ sk_D_1)) | 
% 2.28/2.48       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['111'])).
% 2.28/2.48  thf('150', plain,
% 2.28/2.48      (((m1_subset_1 @ sk_F @ 
% 2.28/2.48         (k1_zfmisc_1 @ 
% 2.28/2.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.48       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['24'])).
% 2.28/2.48  thf('151', plain,
% 2.28/2.48      (((v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1)) | 
% 2.28/2.48       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['104'])).
% 2.28/2.48  thf('152', plain,
% 2.28/2.48      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.48       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['31'])).
% 2.28/2.48  thf('153', plain,
% 2.28/2.48      (((v1_funct_1 @ sk_E_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.28/2.48       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['10'])).
% 2.28/2.48  thf('154', plain,
% 2.28/2.48      (~ ((v2_struct_0 @ sk_D_1)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.28/2.48       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.48      inference('split', [status(esa)], ['52'])).
% 2.28/2.48  thf('155', plain,
% 2.28/2.48      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('split', [status(esa)], ['0'])).
% 2.28/2.48  thf('156', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('157', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('158', plain,
% 2.28/2.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.48         ((v2_struct_0 @ X30)
% 2.28/2.48          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.48          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.48          | (v1_funct_1 @ (sk_E @ X32 @ X30 @ X31))
% 2.28/2.48          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.48          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.48          | (v2_struct_0 @ X32)
% 2.28/2.48          | ~ (l1_pre_topc @ X31)
% 2.28/2.48          | ~ (v2_pre_topc @ X31)
% 2.28/2.48          | (v2_struct_0 @ X31))),
% 2.28/2.48      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.48  thf('159', plain,
% 2.28/2.48      (![X0 : $i]:
% 2.28/2.48         ((v2_struct_0 @ sk_A)
% 2.28/2.48          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.48          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.48          | (v2_struct_0 @ X0)
% 2.28/2.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.48          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.48          | (v1_funct_1 @ (sk_E @ X0 @ sk_B @ sk_A))
% 2.28/2.48          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.48          | (v2_struct_0 @ sk_B))),
% 2.28/2.48      inference('sup-', [status(thm)], ['157', '158'])).
% 2.28/2.48  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('162', plain,
% 2.28/2.48      (![X0 : $i]:
% 2.28/2.48         ((v2_struct_0 @ sk_A)
% 2.28/2.48          | (v2_struct_0 @ X0)
% 2.28/2.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.48          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.48          | (v1_funct_1 @ (sk_E @ X0 @ sk_B @ sk_A))
% 2.28/2.48          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.48          | (v2_struct_0 @ sk_B))),
% 2.28/2.48      inference('demod', [status(thm)], ['159', '160', '161'])).
% 2.28/2.48  thf('163', plain,
% 2.28/2.48      (((v2_struct_0 @ sk_B)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.48        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48        | (v2_struct_0 @ sk_C)
% 2.28/2.48        | (v2_struct_0 @ sk_A))),
% 2.28/2.48      inference('sup-', [status(thm)], ['156', '162'])).
% 2.28/2.48  thf('164', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['155', '163'])).
% 2.28/2.48  thf('165', plain,
% 2.28/2.48      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('split', [status(esa)], ['0'])).
% 2.28/2.48  thf('166', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('167', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('168', plain,
% 2.28/2.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.48         ((v2_struct_0 @ X30)
% 2.28/2.48          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.48          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.48          | (v1_funct_1 @ 
% 2.28/2.48             (k3_tmap_1 @ X31 @ (sk_D @ X32 @ X30 @ X31) @ 
% 2.28/2.48              (k1_tsep_1 @ X31 @ X30 @ X32) @ X32 @ (sk_E @ X32 @ X30 @ X31)))
% 2.28/2.48          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.48          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.48          | (v2_struct_0 @ X32)
% 2.28/2.48          | ~ (l1_pre_topc @ X31)
% 2.28/2.48          | ~ (v2_pre_topc @ X31)
% 2.28/2.48          | (v2_struct_0 @ X31))),
% 2.28/2.48      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.48  thf('169', plain,
% 2.28/2.48      (![X0 : $i]:
% 2.28/2.48         ((v2_struct_0 @ sk_A)
% 2.28/2.48          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.48          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.48          | (v2_struct_0 @ X0)
% 2.28/2.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.48          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.48          | (v1_funct_1 @ 
% 2.28/2.48             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.48              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)))
% 2.28/2.48          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.48          | (v2_struct_0 @ sk_B))),
% 2.28/2.48      inference('sup-', [status(thm)], ['167', '168'])).
% 2.28/2.48  thf('170', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('172', plain,
% 2.28/2.48      (![X0 : $i]:
% 2.28/2.48         ((v2_struct_0 @ sk_A)
% 2.28/2.48          | (v2_struct_0 @ X0)
% 2.28/2.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.48          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.48          | (v1_funct_1 @ 
% 2.28/2.48             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.48              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)))
% 2.28/2.48          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.48          | (v2_struct_0 @ sk_B))),
% 2.28/2.48      inference('demod', [status(thm)], ['169', '170', '171'])).
% 2.28/2.48  thf('173', plain,
% 2.28/2.48      (((v2_struct_0 @ sk_B)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | (v1_funct_1 @ 
% 2.28/2.48           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48            (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48        | (v2_struct_0 @ sk_C)
% 2.28/2.48        | (v2_struct_0 @ sk_A))),
% 2.28/2.48      inference('sup-', [status(thm)], ['166', '172'])).
% 2.28/2.48  thf('174', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v1_funct_1 @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['165', '173'])).
% 2.28/2.48  thf('175', plain,
% 2.28/2.48      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('split', [status(esa)], ['0'])).
% 2.28/2.48  thf('176', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('177', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('178', plain,
% 2.28/2.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.48         ((v2_struct_0 @ X30)
% 2.28/2.48          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.48          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.48          | (v1_funct_2 @ 
% 2.28/2.48             (k3_tmap_1 @ X31 @ (sk_D @ X32 @ X30 @ X31) @ 
% 2.28/2.48              (k1_tsep_1 @ X31 @ X30 @ X32) @ X32 @ (sk_E @ X32 @ X30 @ X31)) @ 
% 2.28/2.48             (u1_struct_0 @ X32) @ (u1_struct_0 @ (sk_D @ X32 @ X30 @ X31)))
% 2.28/2.48          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.48          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.48          | (v2_struct_0 @ X32)
% 2.28/2.48          | ~ (l1_pre_topc @ X31)
% 2.28/2.48          | ~ (v2_pre_topc @ X31)
% 2.28/2.48          | (v2_struct_0 @ X31))),
% 2.28/2.48      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.48  thf('179', plain,
% 2.28/2.48      (![X0 : $i]:
% 2.28/2.48         ((v2_struct_0 @ sk_A)
% 2.28/2.48          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.48          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.48          | (v2_struct_0 @ X0)
% 2.28/2.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.48          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.48          | (v1_funct_2 @ 
% 2.28/2.48             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.48              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.48             (u1_struct_0 @ X0) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.28/2.48          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.48          | (v2_struct_0 @ sk_B))),
% 2.28/2.48      inference('sup-', [status(thm)], ['177', '178'])).
% 2.28/2.48  thf('180', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('181', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('182', plain,
% 2.28/2.48      (![X0 : $i]:
% 2.28/2.48         ((v2_struct_0 @ sk_A)
% 2.28/2.48          | (v2_struct_0 @ X0)
% 2.28/2.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.48          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.48          | (v1_funct_2 @ 
% 2.28/2.48             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.48              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.48             (u1_struct_0 @ X0) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.28/2.48          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.48          | (v2_struct_0 @ sk_B))),
% 2.28/2.48      inference('demod', [status(thm)], ['179', '180', '181'])).
% 2.28/2.48  thf('183', plain,
% 2.28/2.48      (((v2_struct_0 @ sk_B)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | (v1_funct_2 @ 
% 2.28/2.48           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48        | (v2_struct_0 @ sk_C)
% 2.28/2.48        | (v2_struct_0 @ sk_A))),
% 2.28/2.48      inference('sup-', [status(thm)], ['176', '182'])).
% 2.28/2.48  thf('184', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v1_funct_2 @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['175', '183'])).
% 2.28/2.48  thf('185', plain,
% 2.28/2.48      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('split', [status(esa)], ['0'])).
% 2.28/2.48  thf('186', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('187', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('188', plain,
% 2.28/2.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.48         ((v2_struct_0 @ X30)
% 2.28/2.48          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.48          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.48          | (m1_subset_1 @ 
% 2.28/2.48             (k3_tmap_1 @ X31 @ (sk_D @ X32 @ X30 @ X31) @ 
% 2.28/2.48              (k1_tsep_1 @ X31 @ X30 @ X32) @ X32 @ (sk_E @ X32 @ X30 @ X31)) @ 
% 2.28/2.48             (k1_zfmisc_1 @ 
% 2.28/2.48              (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ 
% 2.28/2.48               (u1_struct_0 @ (sk_D @ X32 @ X30 @ X31)))))
% 2.28/2.48          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.48          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.48          | (v2_struct_0 @ X32)
% 2.28/2.48          | ~ (l1_pre_topc @ X31)
% 2.28/2.48          | ~ (v2_pre_topc @ X31)
% 2.28/2.48          | (v2_struct_0 @ X31))),
% 2.28/2.48      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.48  thf('189', plain,
% 2.28/2.48      (![X0 : $i]:
% 2.28/2.48         ((v2_struct_0 @ sk_A)
% 2.28/2.48          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.48          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.48          | (v2_struct_0 @ X0)
% 2.28/2.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.48          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.48          | (m1_subset_1 @ 
% 2.28/2.48             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.48              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.48             (k1_zfmisc_1 @ 
% 2.28/2.48              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.28/2.48               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.28/2.48          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.48          | (v2_struct_0 @ sk_B))),
% 2.28/2.48      inference('sup-', [status(thm)], ['187', '188'])).
% 2.28/2.48  thf('190', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('191', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('192', plain,
% 2.28/2.48      (![X0 : $i]:
% 2.28/2.48         ((v2_struct_0 @ sk_A)
% 2.28/2.48          | (v2_struct_0 @ X0)
% 2.28/2.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.48          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.48          | (m1_subset_1 @ 
% 2.28/2.48             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.48              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.48             (k1_zfmisc_1 @ 
% 2.28/2.48              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 2.28/2.48               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.28/2.48          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.48          | (v2_struct_0 @ sk_B))),
% 2.28/2.48      inference('demod', [status(thm)], ['189', '190', '191'])).
% 2.28/2.48  thf('193', plain,
% 2.28/2.48      (((v2_struct_0 @ sk_B)
% 2.28/2.48        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.48        | (m1_subset_1 @ 
% 2.28/2.48           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48           (k1_zfmisc_1 @ 
% 2.28/2.48            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.48        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48        | (v2_struct_0 @ sk_C)
% 2.28/2.48        | (v2_struct_0 @ sk_A))),
% 2.28/2.48      inference('sup-', [status(thm)], ['186', '192'])).
% 2.28/2.48  thf('194', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (m1_subset_1 @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (k1_zfmisc_1 @ 
% 2.28/2.48             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['185', '193'])).
% 2.28/2.48  thf(redefinition_r2_funct_2, axiom,
% 2.28/2.48    (![A:$i,B:$i,C:$i,D:$i]:
% 2.28/2.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.28/2.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.28/2.48         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.28/2.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.28/2.48       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.28/2.48  thf('195', plain,
% 2.28/2.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.28/2.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 2.28/2.48          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 2.28/2.48          | ~ (v1_funct_1 @ X0)
% 2.28/2.48          | ~ (v1_funct_1 @ X3)
% 2.28/2.48          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 2.28/2.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 2.28/2.48          | (r2_funct_2 @ X1 @ X2 @ X0 @ X3)
% 2.28/2.48          | ((X0) != (X3)))),
% 2.28/2.48      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 2.28/2.48  thf('196', plain,
% 2.28/2.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.28/2.48         ((r2_funct_2 @ X1 @ X2 @ X3 @ X3)
% 2.28/2.48          | ~ (v1_funct_1 @ X3)
% 2.28/2.48          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 2.28/2.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 2.28/2.48      inference('simplify', [status(thm)], ['195'])).
% 2.28/2.48  thf('197', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_B)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | ~ (v1_funct_2 @ 
% 2.28/2.48              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48              (u1_struct_0 @ sk_C) @ 
% 2.28/2.48              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48         | ~ (v1_funct_1 @ 
% 2.28/2.48              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48         | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.48         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['194', '196'])).
% 2.28/2.48  thf('198', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_B)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48         | ~ (v1_funct_1 @ 
% 2.28/2.48              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['184', '197'])).
% 2.28/2.48  thf('199', plain,
% 2.28/2.48      (((~ (v1_funct_1 @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48         | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('simplify', [status(thm)], ['198'])).
% 2.28/2.48  thf('200', plain,
% 2.28/2.48      ((((v2_struct_0 @ sk_B)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_B)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48             (sk_E @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.48         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('sup-', [status(thm)], ['174', '199'])).
% 2.28/2.48  thf('201', plain,
% 2.28/2.48      ((((r2_funct_2 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.48          (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48          (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48           (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48           (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.48          (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.48           (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.48           (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.48         | (v2_struct_0 @ sk_A)
% 2.28/2.48         | (v2_struct_0 @ sk_C)
% 2.28/2.48         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.48         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('simplify', [status(thm)], ['200'])).
% 2.28/2.48  thf('202', plain,
% 2.28/2.48      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.48      inference('split', [status(esa)], ['0'])).
% 2.28/2.48  thf('203', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('204', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.48  thf('205', plain,
% 2.28/2.48      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.48         ((v2_struct_0 @ X30)
% 2.28/2.48          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.48          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.48          | (v1_funct_1 @ 
% 2.28/2.48             (k3_tmap_1 @ X31 @ (sk_D @ X32 @ X30 @ X31) @ 
% 2.28/2.49              (k1_tsep_1 @ X31 @ X30 @ X32) @ X30 @ (sk_E @ X32 @ X30 @ X31)))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('206', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v1_funct_1 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('sup-', [status(thm)], ['204', '205'])).
% 2.28/2.49  thf('207', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('208', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('209', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v1_funct_1 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('demod', [status(thm)], ['206', '207', '208'])).
% 2.28/2.49  thf('210', plain,
% 2.28/2.49      (((v2_struct_0 @ sk_B)
% 2.28/2.49        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49        | (v1_funct_1 @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_A))),
% 2.28/2.49      inference('sup-', [status(thm)], ['203', '209'])).
% 2.28/2.49  thf('211', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['202', '210'])).
% 2.28/2.49  thf('212', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('213', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('214', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('215', plain,
% 2.28/2.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X30)
% 2.28/2.49          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.49          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.49          | (v1_funct_2 @ 
% 2.28/2.49             (k3_tmap_1 @ X31 @ (sk_D @ X32 @ X30 @ X31) @ 
% 2.28/2.49              (k1_tsep_1 @ X31 @ X30 @ X32) @ X30 @ (sk_E @ X32 @ X30 @ X31)) @ 
% 2.28/2.49             (u1_struct_0 @ X30) @ (u1_struct_0 @ (sk_D @ X32 @ X30 @ X31)))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('216', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v1_funct_2 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.49             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('sup-', [status(thm)], ['214', '215'])).
% 2.28/2.49  thf('217', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('219', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v1_funct_2 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.49             (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('demod', [status(thm)], ['216', '217', '218'])).
% 2.28/2.49  thf('220', plain,
% 2.28/2.49      (((v2_struct_0 @ sk_B)
% 2.28/2.49        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49        | (v1_funct_2 @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_A))),
% 2.28/2.49      inference('sup-', [status(thm)], ['213', '219'])).
% 2.28/2.49  thf('221', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_2 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['212', '220'])).
% 2.28/2.49  thf('222', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('223', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('224', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('225', plain,
% 2.28/2.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X30)
% 2.28/2.49          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.49          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.49          | (m1_subset_1 @ 
% 2.28/2.49             (k3_tmap_1 @ X31 @ (sk_D @ X32 @ X30 @ X31) @ 
% 2.28/2.49              (k1_tsep_1 @ X31 @ X30 @ X32) @ X30 @ (sk_E @ X32 @ X30 @ X31)) @ 
% 2.28/2.49             (k1_zfmisc_1 @ 
% 2.28/2.49              (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ 
% 2.28/2.49               (u1_struct_0 @ (sk_D @ X32 @ X30 @ X31)))))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('226', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (m1_subset_1 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.49             (k1_zfmisc_1 @ 
% 2.28/2.49              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('sup-', [status(thm)], ['224', '225'])).
% 2.28/2.49  thf('227', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('228', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('229', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (m1_subset_1 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.49             (k1_zfmisc_1 @ 
% 2.28/2.49              (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('demod', [status(thm)], ['226', '227', '228'])).
% 2.28/2.49  thf('230', plain,
% 2.28/2.49      (((v2_struct_0 @ sk_B)
% 2.28/2.49        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49        | (m1_subset_1 @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49           (k1_zfmisc_1 @ 
% 2.28/2.49            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_A))),
% 2.28/2.49      inference('sup-', [status(thm)], ['223', '229'])).
% 2.28/2.49  thf('231', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (m1_subset_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k1_zfmisc_1 @ 
% 2.28/2.49             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['222', '230'])).
% 2.28/2.49  thf('232', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['165', '173'])).
% 2.28/2.49  thf('233', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_2 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['175', '183'])).
% 2.28/2.49  thf('234', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (m1_subset_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k1_zfmisc_1 @ 
% 2.28/2.49             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['185', '193'])).
% 2.28/2.49  thf('235', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['155', '163'])).
% 2.28/2.49  thf('236', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('237', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('238', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('239', plain,
% 2.28/2.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X30)
% 2.28/2.49          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.49          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.49          | (l1_pre_topc @ (sk_D @ X32 @ X30 @ X31))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('240', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (l1_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('sup-', [status(thm)], ['238', '239'])).
% 2.28/2.49  thf('241', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('242', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('243', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (l1_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('demod', [status(thm)], ['240', '241', '242'])).
% 2.28/2.49  thf('244', plain,
% 2.28/2.49      (((v2_struct_0 @ sk_B)
% 2.28/2.49        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49        | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_A))),
% 2.28/2.49      inference('sup-', [status(thm)], ['237', '243'])).
% 2.28/2.49  thf('245', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['236', '244'])).
% 2.28/2.49  thf('246', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('247', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('248', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('249', plain,
% 2.28/2.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X30)
% 2.28/2.49          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.49          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.49          | (v2_pre_topc @ (sk_D @ X32 @ X30 @ X31))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('250', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v2_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('sup-', [status(thm)], ['248', '249'])).
% 2.28/2.49  thf('251', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('252', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('253', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v2_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('demod', [status(thm)], ['250', '251', '252'])).
% 2.28/2.49  thf('254', plain,
% 2.28/2.49      (((v2_struct_0 @ sk_B)
% 2.28/2.49        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49        | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_A))),
% 2.28/2.49      inference('sup-', [status(thm)], ['247', '253'])).
% 2.28/2.49  thf('255', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['246', '254'])).
% 2.28/2.49  thf('256', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('257', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('258', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('259', plain,
% 2.28/2.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X30)
% 2.28/2.49          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.49          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.49          | (v1_funct_2 @ (sk_E @ X32 @ X30 @ X31) @ 
% 2.28/2.49             (u1_struct_0 @ (k1_tsep_1 @ X31 @ X30 @ X32)) @ 
% 2.28/2.49             (u1_struct_0 @ (sk_D @ X32 @ X30 @ X31)))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('260', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v1_funct_2 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 2.28/2.49             (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('sup-', [status(thm)], ['258', '259'])).
% 2.28/2.49  thf('261', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('262', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('263', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v1_funct_2 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 2.28/2.49             (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('demod', [status(thm)], ['260', '261', '262'])).
% 2.28/2.49  thf('264', plain,
% 2.28/2.49      (((v2_struct_0 @ sk_B)
% 2.28/2.49        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49        | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49           (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_A))),
% 2.28/2.49      inference('sup-', [status(thm)], ['257', '263'])).
% 2.28/2.49  thf('265', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['256', '264'])).
% 2.28/2.49  thf('266', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('267', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('268', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('269', plain,
% 2.28/2.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X30)
% 2.28/2.49          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.49          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.49          | (m1_subset_1 @ (sk_E @ X32 @ X30 @ X31) @ 
% 2.28/2.49             (k1_zfmisc_1 @ 
% 2.28/2.49              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X31 @ X30 @ X32)) @ 
% 2.28/2.49               (u1_struct_0 @ (sk_D @ X32 @ X30 @ X31)))))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('270', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_zfmisc_1 @ 
% 2.28/2.49              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 2.28/2.49               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('sup-', [status(thm)], ['268', '269'])).
% 2.28/2.49  thf('271', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('272', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('273', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (m1_subset_1 @ (sk_E @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_zfmisc_1 @ 
% 2.28/2.49              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ X0)) @ 
% 2.28/2.49               (u1_struct_0 @ (sk_D @ X0 @ sk_B @ sk_A)))))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('demod', [status(thm)], ['270', '271', '272'])).
% 2.28/2.49  thf('274', plain,
% 2.28/2.49      (((v2_struct_0 @ sk_B)
% 2.28/2.49        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49        | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49           (k1_zfmisc_1 @ 
% 2.28/2.49            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49             (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_A))),
% 2.28/2.49      inference('sup-', [status(thm)], ['267', '273'])).
% 2.28/2.49  thf('275', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_zfmisc_1 @ 
% 2.28/2.49             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['266', '274'])).
% 2.28/2.49  thf(d13_tmap_1, axiom,
% 2.28/2.49    (![A:$i]:
% 2.28/2.49     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 2.28/2.49       ( ![B:$i]:
% 2.28/2.49         ( ( ( l1_pre_topc @ B ) & ( v2_pre_topc @ B ) & 
% 2.28/2.49             ( ~( v2_struct_0 @ B ) ) ) =>
% 2.28/2.49           ( ![C:$i]:
% 2.28/2.49             ( ( ( m1_pre_topc @ C @ A ) & ( ~( v2_struct_0 @ C ) ) ) =>
% 2.28/2.49               ( ![D:$i]:
% 2.28/2.49                 ( ( ( m1_pre_topc @ D @ A ) & ( ~( v2_struct_0 @ D ) ) ) =>
% 2.28/2.49                   ( ![E:$i]:
% 2.28/2.49                     ( ( ( m1_subset_1 @
% 2.28/2.49                           E @ 
% 2.28/2.49                           ( k1_zfmisc_1 @
% 2.28/2.49                             ( k2_zfmisc_1 @
% 2.28/2.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 2.28/2.49                         ( v1_funct_2 @
% 2.28/2.49                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.28/2.49                         ( v1_funct_1 @ E ) ) =>
% 2.28/2.49                       ( ![F:$i]:
% 2.28/2.49                         ( ( ( m1_subset_1 @
% 2.28/2.49                               F @ 
% 2.28/2.49                               ( k1_zfmisc_1 @
% 2.28/2.49                                 ( k2_zfmisc_1 @
% 2.28/2.49                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 2.28/2.49                             ( v1_funct_2 @
% 2.28/2.49                               F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 2.28/2.49                             ( v1_funct_1 @ F ) ) =>
% 2.28/2.49                           ( ( ( r2_funct_2 @
% 2.28/2.49                                 ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ 
% 2.28/2.49                                 ( u1_struct_0 @ B ) @ 
% 2.28/2.49                                 ( k3_tmap_1 @
% 2.28/2.49                                   A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ 
% 2.28/2.49                                 ( k3_tmap_1 @
% 2.28/2.49                                   A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) | 
% 2.28/2.49                               ( r1_tsep_1 @ C @ D ) ) =>
% 2.28/2.49                             ( ![G:$i]:
% 2.28/2.49                               ( ( ( m1_subset_1 @
% 2.28/2.49                                     G @ 
% 2.28/2.49                                     ( k1_zfmisc_1 @
% 2.28/2.49                                       ( k2_zfmisc_1 @
% 2.28/2.49                                         ( u1_struct_0 @
% 2.28/2.49                                           ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.28/2.49                                         ( u1_struct_0 @ B ) ) ) ) & 
% 2.28/2.49                                   ( v1_funct_2 @
% 2.28/2.49                                     G @ 
% 2.28/2.49                                     ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.28/2.49                                     ( u1_struct_0 @ B ) ) & 
% 2.28/2.49                                   ( v1_funct_1 @ G ) ) =>
% 2.28/2.49                                 ( ( ( G ) =
% 2.28/2.49                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 2.28/2.49                                   ( ( r2_funct_2 @
% 2.28/2.49                                       ( u1_struct_0 @ D ) @ 
% 2.28/2.49                                       ( u1_struct_0 @ B ) @ 
% 2.28/2.49                                       ( k3_tmap_1 @
% 2.28/2.49                                         A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ 
% 2.28/2.49                                         D @ G ) @ 
% 2.28/2.49                                       F ) & 
% 2.28/2.49                                     ( r2_funct_2 @
% 2.28/2.49                                       ( u1_struct_0 @ C ) @ 
% 2.28/2.49                                       ( u1_struct_0 @ B ) @ 
% 2.28/2.49                                       ( k3_tmap_1 @
% 2.28/2.49                                         A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ 
% 2.28/2.49                                         C @ G ) @ 
% 2.28/2.49                                       E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.28/2.49  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $i > $i > $i > $i > $o).
% 2.28/2.49  thf(zf_stmt_2, axiom,
% 2.28/2.49    (![G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 2.28/2.49     ( ( zip_tseitin_1 @ G @ F @ E @ D @ C @ B @ A ) =>
% 2.28/2.49       ( ( ( G ) = ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 2.28/2.49         ( ( r2_funct_2 @
% 2.28/2.49             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 2.28/2.49             ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ G ) @ E ) & 
% 2.28/2.49           ( r2_funct_2 @
% 2.28/2.49             ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 2.28/2.49             ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ G ) @ F ) ) ) ))).
% 2.28/2.49  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 2.28/2.49  thf(zf_stmt_4, axiom,
% 2.28/2.49    (![F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 2.28/2.49     ( ( ( r1_tsep_1 @ C @ D ) | 
% 2.28/2.49         ( r2_funct_2 @
% 2.28/2.49           ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ 
% 2.28/2.49           ( k3_tmap_1 @ A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ 
% 2.28/2.49           ( k3_tmap_1 @ A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) ) =>
% 2.28/2.49       ( zip_tseitin_0 @ F @ E @ D @ C @ B @ A ) ))).
% 2.28/2.49  thf(zf_stmt_5, axiom,
% 2.28/2.49    (![A:$i]:
% 2.28/2.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.28/2.49       ( ![B:$i]:
% 2.28/2.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 2.28/2.49             ( l1_pre_topc @ B ) ) =>
% 2.28/2.49           ( ![C:$i]:
% 2.28/2.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 2.28/2.49               ( ![D:$i]:
% 2.28/2.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 2.28/2.49                   ( ![E:$i]:
% 2.28/2.49                     ( ( ( v1_funct_1 @ E ) & 
% 2.28/2.49                         ( v1_funct_2 @
% 2.28/2.49                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 2.28/2.49                         ( m1_subset_1 @
% 2.28/2.49                           E @ 
% 2.28/2.49                           ( k1_zfmisc_1 @
% 2.28/2.49                             ( k2_zfmisc_1 @
% 2.28/2.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.28/2.49                       ( ![F:$i]:
% 2.28/2.49                         ( ( ( v1_funct_1 @ F ) & 
% 2.28/2.49                             ( v1_funct_2 @
% 2.28/2.49                               F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 2.28/2.49                             ( m1_subset_1 @
% 2.28/2.49                               F @ 
% 2.28/2.49                               ( k1_zfmisc_1 @
% 2.28/2.49                                 ( k2_zfmisc_1 @
% 2.28/2.49                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.28/2.49                           ( ( zip_tseitin_0 @ F @ E @ D @ C @ B @ A ) =>
% 2.28/2.49                             ( ![G:$i]:
% 2.28/2.49                               ( ( ( v1_funct_1 @ G ) & 
% 2.28/2.49                                   ( v1_funct_2 @
% 2.28/2.49                                     G @ 
% 2.28/2.49                                     ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.28/2.49                                     ( u1_struct_0 @ B ) ) & 
% 2.28/2.49                                   ( m1_subset_1 @
% 2.28/2.49                                     G @ 
% 2.28/2.49                                     ( k1_zfmisc_1 @
% 2.28/2.49                                       ( k2_zfmisc_1 @
% 2.28/2.49                                         ( u1_struct_0 @
% 2.28/2.49                                           ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 2.28/2.49                                         ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.28/2.49                                 ( zip_tseitin_1 @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.28/2.49  thf('276', plain,
% 2.28/2.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X17)
% 2.28/2.49          | ~ (v2_pre_topc @ X17)
% 2.28/2.49          | ~ (l1_pre_topc @ X17)
% 2.28/2.49          | (v2_struct_0 @ X18)
% 2.28/2.49          | ~ (m1_pre_topc @ X18 @ X19)
% 2.28/2.49          | ~ (v1_funct_1 @ X20)
% 2.28/2.49          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 2.28/2.49          | ~ (m1_subset_1 @ X20 @ 
% 2.28/2.49               (k1_zfmisc_1 @ 
% 2.28/2.49                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))))
% 2.28/2.49          | (zip_tseitin_1 @ X21 @ X20 @ X22 @ X18 @ X23 @ X17 @ X19)
% 2.28/2.49          | ~ (m1_subset_1 @ X21 @ 
% 2.28/2.49               (k1_zfmisc_1 @ 
% 2.28/2.49                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X19 @ X23 @ X18)) @ 
% 2.28/2.49                 (u1_struct_0 @ X17))))
% 2.28/2.49          | ~ (v1_funct_2 @ X21 @ 
% 2.28/2.49               (u1_struct_0 @ (k1_tsep_1 @ X19 @ X23 @ X18)) @ 
% 2.28/2.49               (u1_struct_0 @ X17))
% 2.28/2.49          | ~ (v1_funct_1 @ X21)
% 2.28/2.49          | ~ (zip_tseitin_0 @ X20 @ X22 @ X18 @ X23 @ X17 @ X19)
% 2.28/2.49          | ~ (m1_subset_1 @ X22 @ 
% 2.28/2.49               (k1_zfmisc_1 @ 
% 2.28/2.49                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X17))))
% 2.28/2.49          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X17))
% 2.28/2.49          | ~ (v1_funct_1 @ X22)
% 2.28/2.49          | ~ (m1_pre_topc @ X23 @ X19)
% 2.28/2.49          | (v2_struct_0 @ X23)
% 2.28/2.49          | ~ (l1_pre_topc @ X19)
% 2.28/2.49          | ~ (v2_pre_topc @ X19)
% 2.28/2.49          | (v2_struct_0 @ X19))),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.28/2.49  thf('277', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49           | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C @ sk_B @ 
% 2.28/2.49                (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['275', '276'])).
% 2.28/2.49  thf('278', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('279', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('280', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('281', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('282', plain,
% 2.28/2.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 2.28/2.49         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 2.28/2.49          | ~ (r1_tsep_1 @ X7 @ X6))),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.28/2.49  thf('283', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.28/2.49          (zip_tseitin_0 @ X3 @ X2 @ sk_C @ sk_B @ X1 @ X0))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['281', '282'])).
% 2.28/2.49  thf('284', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('285', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('demod', [status(thm)],
% 2.28/2.49                ['277', '278', '279', '280', '283', '284'])).
% 2.28/2.49  thf('286', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['285'])).
% 2.28/2.49  thf('287', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['265', '286'])).
% 2.28/2.49  thf('288', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['287'])).
% 2.28/2.49  thf('289', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['255', '288'])).
% 2.28/2.49  thf('290', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['289'])).
% 2.28/2.49  thf('291', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['245', '290'])).
% 2.28/2.49  thf('292', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['291'])).
% 2.28/2.49  thf('293', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['235', '292'])).
% 2.28/2.49  thf('294', plain,
% 2.28/2.49      ((![X0 : $i, X1 : $i]:
% 2.28/2.49          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X1)
% 2.28/2.49           | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X1 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X1 @ X0 @ sk_C @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['293'])).
% 2.28/2.49  thf('295', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              X0 @ sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (v1_funct_2 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['234', '294'])).
% 2.28/2.49  thf('296', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_2 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              X0 @ sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['295'])).
% 2.28/2.49  thf('297', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              X0 @ sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['233', '296'])).
% 2.28/2.49  thf('298', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              X0 @ sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['297'])).
% 2.28/2.49  thf('299', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              X0 @ sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['232', '298'])).
% 2.28/2.49  thf('300', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              X0 @ sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['299'])).
% 2.28/2.49  thf('301', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v1_funct_2 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (u1_struct_0 @ sk_B) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['231', '300'])).
% 2.28/2.49  thf('302', plain,
% 2.28/2.49      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49         | ~ (v1_funct_2 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (u1_struct_0 @ sk_B) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['301'])).
% 2.28/2.49  thf('303', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['221', '302'])).
% 2.28/2.49  thf('304', plain,
% 2.28/2.49      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['303'])).
% 2.28/2.49  thf('305', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['211', '304'])).
% 2.28/2.49  thf('306', plain,
% 2.28/2.49      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['305'])).
% 2.28/2.49  thf('307', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['202', '210'])).
% 2.28/2.49  thf('308', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_2 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['212', '220'])).
% 2.28/2.49  thf('309', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (m1_subset_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k1_zfmisc_1 @ 
% 2.28/2.49             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['222', '230'])).
% 2.28/2.49  thf('310', plain,
% 2.28/2.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.28/2.49         ((r2_funct_2 @ X1 @ X2 @ X3 @ X3)
% 2.28/2.49          | ~ (v1_funct_1 @ X3)
% 2.28/2.49          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 2.28/2.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['195'])).
% 2.28/2.49  thf('311', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | ~ (v1_funct_2 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (u1_struct_0 @ sk_B) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['309', '310'])).
% 2.28/2.49  thf('312', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['308', '311'])).
% 2.28/2.49  thf('313', plain,
% 2.28/2.49      (((~ (v1_funct_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['312'])).
% 2.28/2.49  thf('314', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (r2_funct_2 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['307', '313'])).
% 2.28/2.49  thf('315', plain,
% 2.28/2.49      ((((r2_funct_2 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49          (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49          (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49           (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49           (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49          (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49           (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49           (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['314'])).
% 2.28/2.49  thf('316', plain,
% 2.28/2.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.28/2.49         (~ (r2_funct_2 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X11) @ 
% 2.28/2.49             (k3_tmap_1 @ X12 @ X11 @ (k1_tsep_1 @ X12 @ X10 @ X13) @ X10 @ X14) @ 
% 2.28/2.49             X15)
% 2.28/2.49          | ~ (r2_funct_2 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 2.28/2.49               (k3_tmap_1 @ X12 @ X11 @ (k1_tsep_1 @ X12 @ X10 @ X13) @ X13 @ 
% 2.28/2.49                X14) @ 
% 2.28/2.49               X16)
% 2.28/2.49          | ((X14) = (k10_tmap_1 @ X12 @ X11 @ X10 @ X13 @ X15 @ X16))
% 2.28/2.49          | ~ (zip_tseitin_1 @ X14 @ X16 @ X15 @ X13 @ X10 @ X11 @ X12))),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.28/2.49  thf('317', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | ~ (zip_tseitin_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ X0 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                sk_C @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 2.28/2.49           | ((sk_E @ sk_C @ sk_B @ sk_A)
% 2.28/2.49               = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ 
% 2.28/2.49                  sk_C @ 
% 2.28/2.49                  (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                   (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49                   (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                  X0))
% 2.28/2.49           | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                X0)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['315', '316'])).
% 2.28/2.49  thf('318', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ((sk_E @ sk_C @ sk_B @ sk_A)
% 2.28/2.49             = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ 
% 2.28/2.49                sk_C @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['306', '317'])).
% 2.28/2.49  thf('319', plain,
% 2.28/2.49      (((((sk_E @ sk_C @ sk_B @ sk_A)
% 2.28/2.49           = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['318'])).
% 2.28/2.49  thf('320', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ((sk_E @ sk_C @ sk_B @ sk_A)
% 2.28/2.49             = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ 
% 2.28/2.49                sk_C @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A))))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['201', '319'])).
% 2.28/2.49  thf('321', plain,
% 2.28/2.49      (((((sk_E @ sk_C @ sk_B @ sk_A)
% 2.28/2.49           = (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['320'])).
% 2.28/2.49  thf('322', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['202', '210'])).
% 2.28/2.49  thf('323', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('324', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('325', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('326', plain,
% 2.28/2.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X30)
% 2.28/2.49          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.49          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.49          | (v5_pre_topc @ 
% 2.28/2.49             (k3_tmap_1 @ X31 @ (sk_D @ X32 @ X30 @ X31) @ 
% 2.28/2.49              (k1_tsep_1 @ X31 @ X30 @ X32) @ X30 @ (sk_E @ X32 @ X30 @ X31)) @ 
% 2.28/2.49             X30 @ (sk_D @ X32 @ X30 @ X31))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('327', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v5_pre_topc @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.49             sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('sup-', [status(thm)], ['325', '326'])).
% 2.28/2.49  thf('328', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('329', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('330', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v5_pre_topc @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.49             sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('demod', [status(thm)], ['327', '328', '329'])).
% 2.28/2.49  thf('331', plain,
% 2.28/2.49      (((v2_struct_0 @ sk_B)
% 2.28/2.49        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49        | (v5_pre_topc @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49           sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_A))),
% 2.28/2.49      inference('sup-', [status(thm)], ['324', '330'])).
% 2.28/2.49  thf('332', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v5_pre_topc @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['323', '331'])).
% 2.28/2.49  thf('333', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_2 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['212', '220'])).
% 2.28/2.49  thf('334', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (m1_subset_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k1_zfmisc_1 @ 
% 2.28/2.49             (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['222', '230'])).
% 2.28/2.49  thf('335', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['246', '254'])).
% 2.28/2.49  thf('336', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['236', '244'])).
% 2.28/2.49  thf('337', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['165', '173'])).
% 2.28/2.49  thf('338', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('339', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('340', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('341', plain,
% 2.28/2.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X30)
% 2.28/2.49          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.49          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.49          | (v5_pre_topc @ 
% 2.28/2.49             (k3_tmap_1 @ X31 @ (sk_D @ X32 @ X30 @ X31) @ 
% 2.28/2.49              (k1_tsep_1 @ X31 @ X30 @ X32) @ X32 @ (sk_E @ X32 @ X30 @ X31)) @ 
% 2.28/2.49             X32 @ (sk_D @ X32 @ X30 @ X31))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('342', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49          | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v5_pre_topc @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.49             X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('sup-', [status(thm)], ['340', '341'])).
% 2.28/2.49  thf('343', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('344', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('345', plain,
% 2.28/2.49      (![X0 : $i]:
% 2.28/2.49         ((v2_struct_0 @ sk_A)
% 2.28/2.49          | (v2_struct_0 @ X0)
% 2.28/2.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ X0)
% 2.28/2.49          | (v5_pre_topc @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ X0) @ X0 @ (sk_E @ X0 @ sk_B @ sk_A)) @ 
% 2.28/2.49             X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 2.28/2.49          | ~ (r1_tsep_1 @ sk_B @ X0)
% 2.28/2.49          | (v2_struct_0 @ sk_B))),
% 2.28/2.49      inference('demod', [status(thm)], ['342', '343', '344'])).
% 2.28/2.49  thf('346', plain,
% 2.28/2.49      (((v2_struct_0 @ sk_B)
% 2.28/2.49        | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49        | (v5_pre_topc @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49           sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49        | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_C)
% 2.28/2.49        | (v2_struct_0 @ sk_A))),
% 2.28/2.49      inference('sup-', [status(thm)], ['339', '345'])).
% 2.28/2.49  thf('347', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v5_pre_topc @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['338', '346'])).
% 2.28/2.49  thf('348', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_2 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (u1_struct_0 @ sk_C) @ (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['175', '183'])).
% 2.28/2.49  thf('349', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (m1_subset_1 @ 
% 2.28/2.49            (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49             (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49            (k1_zfmisc_1 @ 
% 2.28/2.49             (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['185', '193'])).
% 2.28/2.49  thf('350', plain,
% 2.28/2.49      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X44)
% 2.28/2.49          | ~ (v2_pre_topc @ X44)
% 2.28/2.49          | ~ (l1_pre_topc @ X44)
% 2.28/2.49          | ~ (v1_funct_1 @ X45)
% 2.28/2.49          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X44))
% 2.28/2.49          | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49          | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49               (k1_zfmisc_1 @ 
% 2.28/2.49                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X44))))
% 2.28/2.49          | (v5_pre_topc @ 
% 2.28/2.49             (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49             (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44)
% 2.28/2.49          | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49               (k1_zfmisc_1 @ 
% 2.28/2.49                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X44))))
% 2.28/2.49          | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49          | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X44))
% 2.28/2.49          | ~ (v1_funct_1 @ X46)
% 2.28/2.49          | (r3_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('351', plain,
% 2.28/2.49      ((![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49          ((v2_struct_0 @ X44)
% 2.28/2.49           | ~ (v2_pre_topc @ X44)
% 2.28/2.49           | ~ (l1_pre_topc @ X44)
% 2.28/2.49           | ~ (v1_funct_1 @ X45)
% 2.28/2.49           | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X44))
% 2.28/2.49           | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49           | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X44))))
% 2.28/2.49           | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X44))))
% 2.28/2.49           | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49           | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X44))
% 2.28/2.49           | ~ (v1_funct_1 @ X46)
% 2.28/2.49           | (v5_pre_topc @ 
% 2.28/2.49              (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44)))
% 2.28/2.49         <= ((![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('split', [status(esa)], ['350'])).
% 2.28/2.49  thf('352', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v5_pre_topc @ 
% 2.28/2.49              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49               X0 @ 
% 2.28/2.49               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v5_pre_topc @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_2 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['349', '351'])).
% 2.28/2.49  thf('353', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v5_pre_topc @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v5_pre_topc @ 
% 2.28/2.49              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49               X0 @ 
% 2.28/2.49               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['348', '352'])).
% 2.28/2.49  thf('354', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v5_pre_topc @ 
% 2.28/2.49            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49             X0 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v5_pre_topc @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49                sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['353'])).
% 2.28/2.49  thf('355', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v5_pre_topc @ 
% 2.28/2.49              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49               X0 @ 
% 2.28/2.49               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['347', '354'])).
% 2.28/2.49  thf('356', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v5_pre_topc @ 
% 2.28/2.49            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49             X0 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v1_funct_1 @ 
% 2.28/2.49                (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                 (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                 (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['355'])).
% 2.28/2.49  thf('357', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v5_pre_topc @ 
% 2.28/2.49              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49               X0 @ 
% 2.28/2.49               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['337', '356'])).
% 2.28/2.49  thf('358', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v5_pre_topc @ 
% 2.28/2.49            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49             X0 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (l1_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['357'])).
% 2.28/2.49  thf('359', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v5_pre_topc @ 
% 2.28/2.49              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49               X0 @ 
% 2.28/2.49               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['336', '358'])).
% 2.28/2.49  thf('360', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v5_pre_topc @ 
% 2.28/2.49            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49             X0 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v2_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['359'])).
% 2.28/2.49  thf('361', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_B)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | (v5_pre_topc @ 
% 2.28/2.49              (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49               X0 @ 
% 2.28/2.49               (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49                (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49                (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['335', '360'])).
% 2.28/2.49  thf('362', plain,
% 2.28/2.49      ((![X0 : $i]:
% 2.28/2.49          ((v5_pre_topc @ 
% 2.28/2.49            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49             X0 @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (v1_funct_1 @ X0)
% 2.28/2.49           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49           | ~ (v5_pre_topc @ X0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.49                (k1_zfmisc_1 @ 
% 2.28/2.49                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                  (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49           | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49           | (v2_struct_0 @ sk_A)
% 2.28/2.49           | (v2_struct_0 @ sk_C)
% 2.28/2.49           | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49           | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['361'])).
% 2.28/2.49  thf('363', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v5_pre_topc @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v1_funct_2 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (u1_struct_0 @ sk_B) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v5_pre_topc @ 
% 2.28/2.49            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['334', '362'])).
% 2.28/2.49  thf('364', plain,
% 2.28/2.49      ((((v5_pre_topc @ 
% 2.28/2.49          (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v1_funct_2 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              (u1_struct_0 @ sk_B) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v5_pre_topc @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['363'])).
% 2.28/2.49  thf('365', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v5_pre_topc @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v5_pre_topc @ 
% 2.28/2.49            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['333', '364'])).
% 2.28/2.49  thf('366', plain,
% 2.28/2.49      ((((v5_pre_topc @ 
% 2.28/2.49          (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v5_pre_topc @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49              sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['365'])).
% 2.28/2.49  thf('367', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v5_pre_topc @ 
% 2.28/2.49            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['332', '366'])).
% 2.28/2.49  thf('368', plain,
% 2.28/2.49      ((((v5_pre_topc @ 
% 2.28/2.49          (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v1_funct_1 @ 
% 2.28/2.49              (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49               (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49               (sk_E @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['367'])).
% 2.28/2.49  thf('369', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v5_pre_topc @ 
% 2.28/2.49            (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49             (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49              (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup-', [status(thm)], ['322', '368'])).
% 2.28/2.49  thf('370', plain,
% 2.28/2.49      ((((v5_pre_topc @ 
% 2.28/2.49          (k10_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B @ sk_C @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A)) @ 
% 2.28/2.49           (k3_tmap_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C @ 
% 2.28/2.49            (sk_E @ sk_C @ sk_B @ sk_A))) @ 
% 2.28/2.49          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B)))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['369'])).
% 2.28/2.49  thf('371', plain,
% 2.28/2.49      ((((v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49          (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('sup+', [status(thm)], ['321', '370'])).
% 2.28/2.49  thf('372', plain,
% 2.28/2.49      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.49         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.49             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.49                ((v2_struct_0 @ X44)
% 2.28/2.49                 | ~ (v2_pre_topc @ X44)
% 2.28/2.49                 | ~ (l1_pre_topc @ X44)
% 2.28/2.49                 | ~ (v1_funct_1 @ X45)
% 2.28/2.49                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.49                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.49                      (k1_zfmisc_1 @ 
% 2.28/2.49                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                        (u1_struct_0 @ X44))))
% 2.28/2.49                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.49                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.49                      (u1_struct_0 @ X44))
% 2.28/2.49                 | ~ (v1_funct_1 @ X46)
% 2.28/2.49                 | (v5_pre_topc @ 
% 2.28/2.49                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.49                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.49      inference('simplify', [status(thm)], ['371'])).
% 2.28/2.49  thf('373', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49            (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['256', '264'])).
% 2.28/2.49  thf('374', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (m1_subset_1 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49            (k1_zfmisc_1 @ 
% 2.28/2.49             (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['266', '274'])).
% 2.28/2.49  thf('375', plain,
% 2.28/2.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.49         ((v2_struct_0 @ X30)
% 2.28/2.49          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.49          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.49          | ~ (v1_funct_1 @ (sk_E @ X32 @ X30 @ X31))
% 2.28/2.49          | ~ (v1_funct_2 @ (sk_E @ X32 @ X30 @ X31) @ 
% 2.28/2.49               (u1_struct_0 @ (k1_tsep_1 @ X31 @ X30 @ X32)) @ 
% 2.28/2.49               (u1_struct_0 @ (sk_D @ X32 @ X30 @ X31)))
% 2.28/2.49          | ~ (v5_pre_topc @ (sk_E @ X32 @ X30 @ X31) @ 
% 2.28/2.49               (k1_tsep_1 @ X31 @ X30 @ X32) @ (sk_D @ X32 @ X30 @ X31))
% 2.28/2.49          | ~ (m1_subset_1 @ (sk_E @ X32 @ X30 @ X31) @ 
% 2.28/2.49               (k1_zfmisc_1 @ 
% 2.28/2.49                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X31 @ X30 @ X32)) @ 
% 2.28/2.49                 (u1_struct_0 @ (sk_D @ X32 @ X30 @ X31)))))
% 2.28/2.49          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.49          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.49          | (v2_struct_0 @ X32)
% 2.28/2.49          | ~ (l1_pre_topc @ X31)
% 2.28/2.49          | ~ (v2_pre_topc @ X31)
% 2.28/2.49          | (v2_struct_0 @ X31))),
% 2.28/2.49      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.49  thf('376', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | ~ (v2_pre_topc @ sk_A)
% 2.28/2.49         | ~ (l1_pre_topc @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.49         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('sup-', [status(thm)], ['374', '375'])).
% 2.28/2.49  thf('377', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('378', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('379', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('380', plain,
% 2.28/2.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('split', [status(esa)], ['0'])).
% 2.28/2.49  thf('381', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.49  thf('382', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('demod', [status(thm)],
% 2.28/2.49                ['376', '377', '378', '379', '380', '381'])).
% 2.28/2.49  thf('383', plain,
% 2.28/2.49      (((~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | ~ (v1_funct_2 @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.49              (u1_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A)))
% 2.28/2.49         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.49              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.49      inference('simplify', [status(thm)], ['382'])).
% 2.28/2.49  thf('384', plain,
% 2.28/2.49      ((((v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.49         | (v2_struct_0 @ sk_B)
% 2.28/2.49         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_C)
% 2.28/2.49         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.50              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.50         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.28/2.50         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['373', '383'])).
% 2.28/2.50  thf('385', plain,
% 2.28/2.50      (((~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.50         | ~ (v5_pre_topc @ (sk_E @ sk_C @ sk_B @ sk_A) @ 
% 2.28/2.50              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.50      inference('simplify', [status(thm)], ['384'])).
% 2.28/2.50  thf('386', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_B)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.50         | (v2_struct_0 @ sk_B)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | ~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))))
% 2.28/2.50         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('sup-', [status(thm)], ['372', '385'])).
% 2.28/2.50  thf('387', plain,
% 2.28/2.50      (((~ (v1_funct_1 @ (sk_E @ sk_C @ sk_B @ sk_A))
% 2.28/2.50         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_B)))
% 2.28/2.50         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('simplify', [status(thm)], ['386'])).
% 2.28/2.50  thf('388', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_B)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_B)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))))
% 2.28/2.50         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('sup-', [status(thm)], ['164', '387'])).
% 2.28/2.50  thf('389', plain,
% 2.28/2.50      ((((v2_struct_0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_B)))
% 2.28/2.50         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('simplify', [status(thm)], ['388'])).
% 2.28/2.50  thf('390', plain,
% 2.28/2.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.28/2.50         ((v2_struct_0 @ X30)
% 2.28/2.50          | ~ (m1_pre_topc @ X30 @ X31)
% 2.28/2.50          | ~ (r1_tsep_1 @ X30 @ X32)
% 2.28/2.50          | ~ (v2_struct_0 @ (sk_D @ X32 @ X30 @ X31))
% 2.28/2.50          | (r3_tsep_1 @ X31 @ X30 @ X32)
% 2.28/2.50          | ~ (m1_pre_topc @ X32 @ X31)
% 2.28/2.50          | (v2_struct_0 @ X32)
% 2.28/2.50          | ~ (l1_pre_topc @ X31)
% 2.28/2.50          | ~ (v2_pre_topc @ X31)
% 2.28/2.50          | (v2_struct_0 @ X31))),
% 2.28/2.50      inference('cnf', [status(esa)], [t135_tmap_1])).
% 2.28/2.50  thf('391', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_B)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | ~ (v2_pre_topc @ sk_A)
% 2.28/2.50         | ~ (l1_pre_topc @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | ~ (m1_pre_topc @ sk_C @ sk_A)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | ~ (r1_tsep_1 @ sk_B @ sk_C)
% 2.28/2.50         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_B)))
% 2.28/2.50         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('sup-', [status(thm)], ['389', '390'])).
% 2.28/2.50  thf('392', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('393', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('394', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('395', plain,
% 2.28/2.50      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 2.28/2.50      inference('split', [status(esa)], ['0'])).
% 2.28/2.50  thf('396', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('397', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_B)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_B)))
% 2.28/2.50         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('demod', [status(thm)],
% 2.28/2.50                ['391', '392', '393', '394', '395', '396'])).
% 2.28/2.50  thf('398', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_C)
% 2.28/2.50         | (r3_tsep_1 @ sk_A @ sk_B @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_B)))
% 2.28/2.50         <= (((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('simplify', [status(thm)], ['397'])).
% 2.28/2.50  thf('399', plain,
% 2.28/2.50      ((~ (r3_tsep_1 @ sk_A @ sk_B @ sk_C))
% 2.28/2.50         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 2.28/2.50      inference('split', [status(esa)], ['10'])).
% 2.28/2.50  thf('400', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 2.28/2.50         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.50             ((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('sup-', [status(thm)], ['398', '399'])).
% 2.28/2.50  thf('401', plain, (~ (v2_struct_0 @ sk_B)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('402', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 2.28/2.50         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.50             ((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('clc', [status(thm)], ['400', '401'])).
% 2.28/2.50  thf('403', plain, (~ (v2_struct_0 @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('404', plain,
% 2.28/2.50      (((v2_struct_0 @ sk_C))
% 2.28/2.50         <= (~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) & 
% 2.28/2.50             ((r1_tsep_1 @ sk_B @ sk_C)) & 
% 2.28/2.50             (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50                ((v2_struct_0 @ X44)
% 2.28/2.50                 | ~ (v2_pre_topc @ X44)
% 2.28/2.50                 | ~ (l1_pre_topc @ X44)
% 2.28/2.50                 | ~ (v1_funct_1 @ X45)
% 2.28/2.50                 | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50                 | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                      (k1_zfmisc_1 @ 
% 2.28/2.50                       (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                        (u1_struct_0 @ X44))))
% 2.28/2.50                 | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50                 | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                      (u1_struct_0 @ X44))
% 2.28/2.50                 | ~ (v1_funct_1 @ X46)
% 2.28/2.50                 | (v5_pre_topc @ 
% 2.28/2.50                    (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50                    (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))))),
% 2.28/2.50      inference('clc', [status(thm)], ['402', '403'])).
% 2.28/2.50  thf('405', plain, (~ (v2_struct_0 @ sk_C)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('406', plain,
% 2.28/2.50      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.28/2.50       ~
% 2.28/2.50       (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50          ((v2_struct_0 @ X44)
% 2.28/2.50           | ~ (v2_pre_topc @ X44)
% 2.28/2.50           | ~ (l1_pre_topc @ X44)
% 2.28/2.50           | ~ (v1_funct_1 @ X45)
% 2.28/2.50           | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X44))
% 2.28/2.50           | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50           | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                (k1_zfmisc_1 @ 
% 2.28/2.50                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X44))))
% 2.28/2.50           | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                (k1_zfmisc_1 @ 
% 2.28/2.50                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X44))))
% 2.28/2.50           | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50           | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X44))
% 2.28/2.50           | ~ (v1_funct_1 @ X46)
% 2.28/2.50           | (v5_pre_topc @ 
% 2.28/2.50              (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44))) | 
% 2.28/2.50       ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.50      inference('sup-', [status(thm)], ['404', '405'])).
% 2.28/2.50  thf('407', plain,
% 2.28/2.50      (((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.28/2.50       (![X44 : $i, X45 : $i, X46 : $i]:
% 2.28/2.50          ((v2_struct_0 @ X44)
% 2.28/2.50           | ~ (v2_pre_topc @ X44)
% 2.28/2.50           | ~ (l1_pre_topc @ X44)
% 2.28/2.50           | ~ (v1_funct_1 @ X45)
% 2.28/2.50           | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X44))
% 2.28/2.50           | ~ (v5_pre_topc @ X45 @ sk_C @ X44)
% 2.28/2.50           | ~ (m1_subset_1 @ X45 @ 
% 2.28/2.50                (k1_zfmisc_1 @ 
% 2.28/2.50                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X44))))
% 2.28/2.50           | ~ (m1_subset_1 @ X46 @ 
% 2.28/2.50                (k1_zfmisc_1 @ 
% 2.28/2.50                 (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X44))))
% 2.28/2.50           | ~ (v5_pre_topc @ X46 @ sk_B @ X44)
% 2.28/2.50           | ~ (v1_funct_2 @ X46 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X44))
% 2.28/2.50           | ~ (v1_funct_1 @ X46)
% 2.28/2.50           | (v5_pre_topc @ 
% 2.28/2.50              (k10_tmap_1 @ sk_A @ X44 @ sk_B @ sk_C @ X46 @ X45) @ 
% 2.28/2.50              (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ X44)))),
% 2.28/2.50      inference('split', [status(esa)], ['350'])).
% 2.28/2.50  thf('408', plain,
% 2.28/2.50      (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50         (k1_zfmisc_1 @ 
% 2.28/2.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.50       ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | ~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 2.28/2.50      inference('split', [status(esa)], ['33'])).
% 2.28/2.50  thf('409', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('410', plain, (((v1_funct_1 @ sk_F)) <= (((v1_funct_1 @ sk_F)))),
% 2.28/2.50      inference('split', [status(esa)], ['20'])).
% 2.28/2.50  thf('411', plain,
% 2.28/2.50      (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))
% 2.28/2.50         <= (((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.50      inference('split', [status(esa)], ['22'])).
% 2.28/2.50  thf('412', plain,
% 2.28/2.50      (((m1_subset_1 @ sk_F @ 
% 2.28/2.50         (k1_zfmisc_1 @ 
% 2.28/2.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1)))))
% 2.28/2.50         <= (((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.50      inference('split', [status(esa)], ['24'])).
% 2.28/2.50  thf('413', plain, (((v1_funct_1 @ sk_E_1)) <= (((v1_funct_1 @ sk_E_1)))),
% 2.28/2.50      inference('split', [status(esa)], ['10'])).
% 2.28/2.50  thf('414', plain, (((v2_pre_topc @ sk_D_1)) <= (((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('split', [status(esa)], ['28'])).
% 2.28/2.50  thf('415', plain, (((l1_pre_topc @ sk_D_1)) <= (((l1_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('split', [status(esa)], ['26'])).
% 2.28/2.50  thf('416', plain,
% 2.28/2.50      (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 2.28/2.50         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))))),
% 2.28/2.50      inference('split', [status(esa)], ['31'])).
% 2.28/2.50  thf('417', plain,
% 2.28/2.50      (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50         (k1_zfmisc_1 @ 
% 2.28/2.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))))
% 2.28/2.50         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.50      inference('split', [status(esa)], ['33'])).
% 2.28/2.50  thf('418', plain,
% 2.28/2.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.28/2.50         (~ (m1_subset_1 @ X24 @ 
% 2.28/2.50             (k1_zfmisc_1 @ 
% 2.28/2.50              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))))
% 2.28/2.50          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 2.28/2.50          | ~ (v1_funct_1 @ X24)
% 2.28/2.50          | ~ (m1_pre_topc @ X27 @ X28)
% 2.28/2.50          | (v2_struct_0 @ X27)
% 2.28/2.50          | ~ (m1_pre_topc @ X25 @ X28)
% 2.28/2.50          | (v2_struct_0 @ X25)
% 2.28/2.50          | ~ (l1_pre_topc @ X26)
% 2.28/2.50          | ~ (v2_pre_topc @ X26)
% 2.28/2.50          | (v2_struct_0 @ X26)
% 2.28/2.50          | ~ (l1_pre_topc @ X28)
% 2.28/2.50          | ~ (v2_pre_topc @ X28)
% 2.28/2.50          | (v2_struct_0 @ X28)
% 2.28/2.50          | ~ (v1_funct_1 @ X29)
% 2.28/2.50          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 2.28/2.50          | ~ (m1_subset_1 @ X29 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 2.28/2.50          | (v1_funct_1 @ (k10_tmap_1 @ X28 @ X26 @ X25 @ X27 @ X24 @ X29)))),
% 2.28/2.50      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 2.28/2.50  thf('419', plain,
% 2.28/2.50      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.50          ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0))
% 2.28/2.50           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.50                (k1_zfmisc_1 @ 
% 2.28/2.50                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.50           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.50           | ~ (v1_funct_1 @ X0)
% 2.28/2.50           | (v2_struct_0 @ X2)
% 2.28/2.50           | ~ (v2_pre_topc @ X2)
% 2.28/2.50           | ~ (l1_pre_topc @ X2)
% 2.28/2.50           | (v2_struct_0 @ sk_D_1)
% 2.28/2.50           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.50           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.50           | (v2_struct_0 @ sk_B)
% 2.28/2.50           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.28/2.50           | (v2_struct_0 @ X1)
% 2.28/2.50           | ~ (m1_pre_topc @ X1 @ X2)
% 2.28/2.50           | ~ (v1_funct_1 @ sk_E_1)
% 2.28/2.50           | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50                (u1_struct_0 @ sk_D_1))))
% 2.28/2.50         <= (((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.50      inference('sup-', [status(thm)], ['417', '418'])).
% 2.28/2.50  thf('420', plain,
% 2.28/2.50      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.50          (~ (v1_funct_1 @ sk_E_1)
% 2.28/2.50           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.50           | (v2_struct_0 @ X1)
% 2.28/2.50           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.50           | (v2_struct_0 @ sk_B)
% 2.28/2.50           | ~ (l1_pre_topc @ sk_D_1)
% 2.28/2.50           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.50           | (v2_struct_0 @ sk_D_1)
% 2.28/2.50           | ~ (l1_pre_topc @ X0)
% 2.28/2.50           | ~ (v2_pre_topc @ X0)
% 2.28/2.50           | (v2_struct_0 @ X0)
% 2.28/2.50           | ~ (v1_funct_1 @ X2)
% 2.28/2.50           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.50           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.50                (k1_zfmisc_1 @ 
% 2.28/2.50                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.50           | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2))))
% 2.28/2.50         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))))),
% 2.28/2.50      inference('sup-', [status(thm)], ['416', '419'])).
% 2.28/2.50  thf('421', plain,
% 2.28/2.50      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.50          ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0))
% 2.28/2.50           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.50                (k1_zfmisc_1 @ 
% 2.28/2.50                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.50           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.50           | ~ (v1_funct_1 @ X0)
% 2.28/2.50           | (v2_struct_0 @ X2)
% 2.28/2.50           | ~ (v2_pre_topc @ X2)
% 2.28/2.50           | ~ (l1_pre_topc @ X2)
% 2.28/2.50           | (v2_struct_0 @ sk_D_1)
% 2.28/2.50           | ~ (v2_pre_topc @ sk_D_1)
% 2.28/2.50           | (v2_struct_0 @ sk_B)
% 2.28/2.50           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.28/2.50           | (v2_struct_0 @ X1)
% 2.28/2.50           | ~ (m1_pre_topc @ X1 @ X2)
% 2.28/2.50           | ~ (v1_funct_1 @ sk_E_1)))
% 2.28/2.50         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['415', '420'])).
% 2.28/2.50  thf('422', plain,
% 2.28/2.50      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.50          (~ (v1_funct_1 @ sk_E_1)
% 2.28/2.50           | ~ (m1_pre_topc @ X1 @ X0)
% 2.28/2.50           | (v2_struct_0 @ X1)
% 2.28/2.50           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.50           | (v2_struct_0 @ sk_B)
% 2.28/2.50           | (v2_struct_0 @ sk_D_1)
% 2.28/2.50           | ~ (l1_pre_topc @ X0)
% 2.28/2.50           | ~ (v2_pre_topc @ X0)
% 2.28/2.50           | (v2_struct_0 @ X0)
% 2.28/2.50           | ~ (v1_funct_1 @ X2)
% 2.28/2.50           | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.50           | ~ (m1_subset_1 @ X2 @ 
% 2.28/2.50                (k1_zfmisc_1 @ 
% 2.28/2.50                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.50           | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X2))))
% 2.28/2.50         <= (((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['414', '421'])).
% 2.28/2.50  thf('423', plain,
% 2.28/2.50      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.28/2.50          ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_D_1 @ sk_B @ X1 @ sk_E_1 @ X0))
% 2.28/2.50           | ~ (m1_subset_1 @ X0 @ 
% 2.28/2.50                (k1_zfmisc_1 @ 
% 2.28/2.50                 (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))))
% 2.28/2.50           | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 2.28/2.50           | ~ (v1_funct_1 @ X0)
% 2.28/2.50           | (v2_struct_0 @ X2)
% 2.28/2.50           | ~ (v2_pre_topc @ X2)
% 2.28/2.50           | ~ (l1_pre_topc @ X2)
% 2.28/2.50           | (v2_struct_0 @ sk_D_1)
% 2.28/2.50           | (v2_struct_0 @ sk_B)
% 2.28/2.50           | ~ (m1_pre_topc @ sk_B @ X2)
% 2.28/2.50           | (v2_struct_0 @ X1)
% 2.28/2.50           | ~ (m1_pre_topc @ X1 @ X2)))
% 2.28/2.50         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['413', '422'])).
% 2.28/2.50  thf('424', plain,
% 2.28/2.50      ((![X0 : $i]:
% 2.28/2.50          (~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.50           | (v2_struct_0 @ sk_C)
% 2.28/2.50           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.50           | (v2_struct_0 @ sk_B)
% 2.28/2.50           | (v2_struct_0 @ sk_D_1)
% 2.28/2.50           | ~ (l1_pre_topc @ X0)
% 2.28/2.50           | ~ (v2_pre_topc @ X0)
% 2.28/2.50           | (v2_struct_0 @ X0)
% 2.28/2.50           | ~ (v1_funct_1 @ sk_F)
% 2.28/2.50           | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50                (u1_struct_0 @ sk_D_1))
% 2.28/2.50           | (v1_funct_1 @ 
% 2.28/2.50              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))))
% 2.28/2.50         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['412', '423'])).
% 2.28/2.50  thf('425', plain,
% 2.28/2.50      ((![X0 : $i]:
% 2.28/2.50          ((v1_funct_1 @ 
% 2.28/2.50            (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))
% 2.28/2.50           | ~ (v1_funct_1 @ sk_F)
% 2.28/2.50           | (v2_struct_0 @ X0)
% 2.28/2.50           | ~ (v2_pre_topc @ X0)
% 2.28/2.50           | ~ (l1_pre_topc @ X0)
% 2.28/2.50           | (v2_struct_0 @ sk_D_1)
% 2.28/2.50           | (v2_struct_0 @ sk_B)
% 2.28/2.50           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.50           | (v2_struct_0 @ sk_C)
% 2.28/2.50           | ~ (m1_pre_topc @ sk_C @ X0)))
% 2.28/2.50         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['411', '424'])).
% 2.28/2.50  thf('426', plain,
% 2.28/2.50      ((![X0 : $i]:
% 2.28/2.50          (~ (m1_pre_topc @ sk_C @ X0)
% 2.28/2.50           | (v2_struct_0 @ sk_C)
% 2.28/2.50           | ~ (m1_pre_topc @ sk_B @ X0)
% 2.28/2.50           | (v2_struct_0 @ sk_B)
% 2.28/2.50           | (v2_struct_0 @ sk_D_1)
% 2.28/2.50           | ~ (l1_pre_topc @ X0)
% 2.28/2.50           | ~ (v2_pre_topc @ X0)
% 2.28/2.50           | (v2_struct_0 @ X0)
% 2.28/2.50           | (v1_funct_1 @ 
% 2.28/2.50              (k10_tmap_1 @ X0 @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))))
% 2.28/2.50         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['410', '425'])).
% 2.28/2.50  thf('427', plain,
% 2.28/2.50      ((((v1_funct_1 @ 
% 2.28/2.50          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | ~ (v2_pre_topc @ sk_A)
% 2.28/2.50         | ~ (l1_pre_topc @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_D_1)
% 2.28/2.50         | (v2_struct_0 @ sk_B)
% 2.28/2.50         | ~ (m1_pre_topc @ sk_B @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_C)))
% 2.28/2.50         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['409', '426'])).
% 2.28/2.50  thf('428', plain, ((v2_pre_topc @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('429', plain, ((l1_pre_topc @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('430', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('431', plain,
% 2.28/2.50      ((((v1_funct_1 @ 
% 2.28/2.50          (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))
% 2.28/2.50         | (v2_struct_0 @ sk_A)
% 2.28/2.50         | (v2_struct_0 @ sk_D_1)
% 2.28/2.50         | (v2_struct_0 @ sk_B)
% 2.28/2.50         | (v2_struct_0 @ sk_C)))
% 2.28/2.50         <= (((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('demod', [status(thm)], ['427', '428', '429', '430'])).
% 2.28/2.50  thf('432', plain,
% 2.28/2.50      ((~ (v1_funct_1 @ 
% 2.28/2.50           (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F)))
% 2.28/2.50         <= (~
% 2.28/2.50             ((v1_funct_1 @ 
% 2.28/2.50               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))))),
% 2.28/2.50      inference('split', [status(esa)], ['49'])).
% 2.28/2.50  thf('433', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_C)
% 2.28/2.50         | (v2_struct_0 @ sk_B)
% 2.28/2.50         | (v2_struct_0 @ sk_D_1)
% 2.28/2.50         | (v2_struct_0 @ sk_A)))
% 2.28/2.50         <= (~
% 2.28/2.50             ((v1_funct_1 @ 
% 2.28/2.50               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['431', '432'])).
% 2.28/2.50  thf('434', plain,
% 2.28/2.50      ((~ (v2_struct_0 @ sk_D_1)) <= (~ ((v2_struct_0 @ sk_D_1)))),
% 2.28/2.50      inference('split', [status(esa)], ['52'])).
% 2.28/2.50  thf('435', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 2.28/2.50         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.50             ~
% 2.28/2.50             ((v1_funct_1 @ 
% 2.28/2.50               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('sup-', [status(thm)], ['433', '434'])).
% 2.28/2.50  thf('436', plain, (~ (v2_struct_0 @ sk_A)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('437', plain,
% 2.28/2.50      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 2.28/2.50         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.50             ~
% 2.28/2.50             ((v1_funct_1 @ 
% 2.28/2.50               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('clc', [status(thm)], ['435', '436'])).
% 2.28/2.50  thf('438', plain, (~ (v2_struct_0 @ sk_C)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('439', plain,
% 2.28/2.50      (((v2_struct_0 @ sk_B))
% 2.28/2.50         <= (~ ((v2_struct_0 @ sk_D_1)) & 
% 2.28/2.50             ~
% 2.28/2.50             ((v1_funct_1 @ 
% 2.28/2.50               (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_E_1)) & 
% 2.28/2.50             ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((m1_subset_1 @ sk_F @ 
% 2.28/2.50               (k1_zfmisc_1 @ 
% 2.28/2.50                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) & 
% 2.28/2.50             ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ 
% 2.28/2.50               (u1_struct_0 @ sk_D_1))) & 
% 2.28/2.50             ((v1_funct_1 @ sk_F)) & 
% 2.28/2.50             ((l1_pre_topc @ sk_D_1)) & 
% 2.28/2.50             ((v2_pre_topc @ sk_D_1)))),
% 2.28/2.50      inference('clc', [status(thm)], ['437', '438'])).
% 2.28/2.50  thf('440', plain, (~ (v2_struct_0 @ sk_B)),
% 2.28/2.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.28/2.50  thf('441', plain,
% 2.28/2.50      (((v1_funct_1 @ 
% 2.28/2.50         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) | 
% 2.28/2.50       ~
% 2.28/2.50       ((m1_subset_1 @ sk_E_1 @ 
% 2.28/2.50         (k1_zfmisc_1 @ 
% 2.28/2.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.50       ~ ((v2_pre_topc @ sk_D_1)) | ~ ((v1_funct_1 @ sk_F)) | 
% 2.28/2.50       ~ ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.50       ~
% 2.28/2.50       ((m1_subset_1 @ sk_F @ 
% 2.28/2.50         (k1_zfmisc_1 @ 
% 2.28/2.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.50       ~
% 2.28/2.50       ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.50       ~ ((v1_funct_1 @ sk_E_1)) | ~ ((l1_pre_topc @ sk_D_1)) | 
% 2.28/2.50       ((v2_struct_0 @ sk_D_1))),
% 2.28/2.50      inference('sup-', [status(thm)], ['439', '440'])).
% 2.28/2.50  thf('442', plain,
% 2.28/2.50      (~
% 2.28/2.50       ((v1_funct_1 @ 
% 2.28/2.50         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F))) | 
% 2.28/2.50       ~
% 2.28/2.50       ((m1_subset_1 @ 
% 2.28/2.50         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.50         (k1_zfmisc_1 @ 
% 2.28/2.50          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.50           (u1_struct_0 @ sk_D_1))))) | 
% 2.28/2.50       ~ ((r1_tsep_1 @ sk_B @ sk_C)) | ~ ((r3_tsep_1 @ sk_A @ sk_B @ sk_C)) | 
% 2.28/2.50       ~
% 2.28/2.50       ((v1_funct_2 @ 
% 2.28/2.50         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.50         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 2.28/2.50         (u1_struct_0 @ sk_D_1))) | 
% 2.28/2.50       ~
% 2.28/2.50       ((v5_pre_topc @ 
% 2.28/2.50         (k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F) @ 
% 2.28/2.50         (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D_1))),
% 2.28/2.50      inference('split', [status(esa)], ['49'])).
% 2.28/2.50  thf('443', plain, ($false),
% 2.28/2.50      inference('sat_resolution*', [status(thm)],
% 2.28/2.50                ['1', '18', '60', '93', '144', '145', '146', '147', '148', 
% 2.28/2.50                 '149', '150', '151', '152', '153', '154', '406', '407', 
% 2.28/2.50                 '408', '441', '442'])).
% 2.28/2.50  
% 2.28/2.50  % SZS output end Refutation
% 2.28/2.50  
% 2.28/2.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
