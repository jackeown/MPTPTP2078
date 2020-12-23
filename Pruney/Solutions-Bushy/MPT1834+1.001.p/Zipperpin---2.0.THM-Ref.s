%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1834+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z4PfxsuQT3

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:22 EST 2020

% Result     : Theorem 4.35s
% Output     : Refutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  613 (3336 expanded)
%              Number of leaves         :   39 ( 924 expanded)
%              Depth                    :   52
%              Number of atoms          : 25118 (190010 expanded)
%              Number of equality atoms :   30 (  80 expanded)
%              Maximal formula depth    :   35 (  12 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r3_tsep_1_type,type,(
    r3_tsep_1: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

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

thf('0',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_funct_1 @ sk_F )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( l1_pre_topc @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( v2_pre_topc @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['15'])).

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

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X4 @ X7 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X7 @ X5 @ X4 @ X6 @ X3 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X7 @ X4 @ X6 ) ) @ ( u1_struct_0 @ X5 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('18',plain,
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
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
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
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,
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
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,
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
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,
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
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,
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
    inference('sup-',[status(thm)],['6','22'])).

thf('24',plain,
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
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,
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
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,
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
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
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
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
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
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
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
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
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
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
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
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('45',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('47',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('48',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('49',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('50',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X4 @ X7 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X7 @ X5 @ X4 @ X6 @ X3 @ X8 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X7 @ X4 @ X6 ) ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('53',plain,
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
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
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
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
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
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
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
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
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
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,
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
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,
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
    inference('sup-',[status(thm)],['45','58'])).

thf('60',plain,
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
    inference('sup-',[status(thm)],['44','59'])).

thf('61',plain,
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
    inference('sup-',[status(thm)],['43','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
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
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['31'])).

thf('67',plain,
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
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['34'])).

thf('69',plain,
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
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
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
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
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
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
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
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('78',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('80',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('81',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('82',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('85',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X4 @ X7 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X7 @ X5 @ X4 @ X6 @ X3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('86',plain,
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
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
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
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
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
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,
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
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,
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
    inference('sup-',[status(thm)],['80','89'])).

thf('91',plain,
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
    inference('sup-',[status(thm)],['79','90'])).

thf('92',plain,
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
    inference('sup-',[status(thm)],['78','91'])).

thf('93',plain,
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
    inference('sup-',[status(thm)],['77','92'])).

thf('94',plain,
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
    inference('sup-',[status(thm)],['76','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
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
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) ) ),
    inference(split,[status(esa)],['31'])).

thf('100',plain,
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
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['34'])).

thf('102',plain,
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
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
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
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
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
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['109'])).

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

thf('111',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X38 )
      | ~ ( r3_tsep_1 @ X38 @ X37 @ X39 )
      | ( r4_tsep_1 @ X38 @ X37 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t85_tsep_1])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r4_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,
    ( ( v1_funct_1 @ sk_E_1 )
   <= ( v1_funct_1 @ sk_E_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('119',plain,
    ( ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['109'])).

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

thf('120',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ( r1_tsep_1 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,
    ( ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
   <= ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['127'])).

thf('129',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('130',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('131',plain,
    ( ( l1_pre_topc @ sk_D_1 )
   <= ( l1_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('132',plain,
    ( ( v2_pre_topc @ sk_D_1 )
   <= ( v2_pre_topc @ sk_D_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('133',plain,
    ( ( v1_funct_1 @ sk_F )
   <= ( v1_funct_1 @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('134',plain,
    ( ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
   <= ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['134'])).

thf('136',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('137',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
   <= ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ) ),
    inference(split,[status(esa)],['5'])).

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

thf('138',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v5_pre_topc @ X34 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X33 @ X31 @ X35 @ X32 @ X36 @ X34 ) @ ( k1_tsep_1 @ X33 @ X35 @ X32 ) @ X31 )
      | ~ ( r4_tsep_1 @ X33 @ X35 @ X32 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v5_pre_topc @ X36 @ X35 @ X31 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( r1_tsep_1 @ X35 @ X32 )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t145_tmap_1])).

thf('139',plain,
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
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
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
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,
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
    inference('sup-',[status(thm)],['135','140'])).

thf('142',plain,
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
    inference('sup-',[status(thm)],['133','141'])).

thf('143',plain,
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
    inference('sup-',[status(thm)],['132','142'])).

thf('144',plain,
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
    inference('sup-',[status(thm)],['131','143'])).

thf('145',plain,
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
    inference('sup-',[status(thm)],['130','144'])).

thf('146',plain,
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
    inference('sup-',[status(thm)],['129','145'])).

thf('147',plain,
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
    inference('sup-',[status(thm)],['128','146'])).

thf('148',plain,
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
    inference('sup-',[status(thm)],['126','147'])).

thf('149',plain,
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
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
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
    inference('sup-',[status(thm)],['118','149'])).

thf('151',plain,
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
    inference('sup-',[status(thm)],['117','150'])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
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
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,
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
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['31'])).

thf('159',plain,
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
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
   <= ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(split,[status(esa)],['34'])).

thf('161',plain,
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
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
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
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
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
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( v2_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( l1_pre_topc @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ( v2_struct_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( v2_pre_topc @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('169',plain,
    ( ( l1_pre_topc @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('170',plain,
    ( ( v1_funct_1 @ sk_F )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['1'])).

thf('171',plain,
    ( ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('172',plain,
    ( ( v5_pre_topc @ sk_F @ sk_C @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['134'])).

thf('173',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('174',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['15'])).

thf('175',plain,
    ( ( v5_pre_topc @ sk_E_1 @ sk_B @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['127'])).

thf('176',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('177',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('178',plain,
    ( ~ ( v2_struct_0 @ sk_D_1 )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('179',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['109'])).

thf('180',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('181',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('182',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tsep_1 @ sk_B @ sk_C )
      & ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C )
    | ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_D_1 @ sk_B @ sk_C @ sk_E_1 @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['31'])).

thf('190',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ! [X40: $i,X41: $i,X42: $i] :
        ( ( v2_struct_0 @ X40 )
        | ~ ( v2_pre_topc @ X40 )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v1_funct_1 @ X41 )
        | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
        | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
        | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
        | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
        | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
        | ~ ( v1_funct_1 @ X42 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['190'])).

thf('192',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['109'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('193',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('194',plain,
    ( ( ( r1_tsep_1 @ sk_C @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('196',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('197',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['197','198'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('200',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('201',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('204',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('208',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('210',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( v1_funct_1 @ ( sk_E @ X23 @ X21 @ X22 ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_1 @ ( sk_E @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['210','216'])).

thf('218',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['209','217'])).

thf('219',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ( k1_tsep_1 @ A @ B @ C )
        = ( k1_tsep_1 @ A @ C @ B ) ) ) )).

thf('221',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( ( k1_tsep_1 @ X1 @ X0 @ X2 )
        = ( k1_tsep_1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k1_tsep_1])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( ( k1_tsep_1 @ sk_A @ sk_C @ X0 )
        = ( k1_tsep_1 @ sk_A @ X0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( ( k1_tsep_1 @ sk_A @ sk_C @ X0 )
        = ( k1_tsep_1 @ sk_A @ X0 @ sk_C ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('226',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('227',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('229',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X22 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ X21 @ ( sk_E @ X23 @ X21 @ X22 ) ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C @ ( sk_E @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C @ ( sk_E @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['229','235'])).

thf('237',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['228','236'])).

thf('238',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('239',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X22 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ X21 @ ( sk_E @ X23 @ X21 @ X22 ) ) @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( sk_D @ X23 @ X21 @ X22 ) ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['239','245'])).

thf('247',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['238','246'])).

thf('248',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('249',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X22 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ X21 @ ( sk_E @ X23 @ X21 @ X22 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( sk_D @ X23 @ X21 @ X22 ) ) ) ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('252',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['249','255'])).

thf('257',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['248','256'])).

thf('258',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('259',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( v2_pre_topc @ ( sk_D @ X23 @ X21 @ X22 ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v2_pre_topc @ ( sk_D @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v2_pre_topc @ ( sk_D @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('266',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['259','265'])).

thf('267',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['258','266'])).

thf('268',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('269',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( l1_pre_topc @ ( sk_D @ X23 @ X21 @ X22 ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( l1_pre_topc @ ( sk_D @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( l1_pre_topc @ ( sk_D @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['272','273','274'])).

thf('276',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['269','275'])).

thf('277',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['268','276'])).

thf('278',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('279',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X22 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ X23 @ ( sk_E @ X23 @ X21 @ X22 ) ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('282',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('286',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['279','285'])).

thf('287',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['278','286'])).

thf('288',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('289',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X22 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ X23 @ ( sk_E @ X23 @ X21 @ X22 ) ) @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ ( sk_D @ X23 @ X21 @ X22 ) ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('292',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['292','293','294'])).

thf('296',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['289','295'])).

thf('297',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['288','296'])).

thf('298',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('299',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X22 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ X23 @ ( sk_E @ X23 @ X21 @ X22 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ ( sk_D @ X23 @ X21 @ X22 ) ) ) ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('302',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['300','301'])).

thf('303',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['302','303','304'])).

thf('306',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['299','305'])).

thf('307',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['298','306'])).

thf('308',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X4 @ X7 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X7 @ X5 @ X4 @ X6 @ X3 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('309',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['309'])).

thf('311',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['297','310'])).

thf('312',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['287','312'])).

thf('314',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['313'])).

thf('315',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['277','314'])).

thf('316',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ~ ( l1_pre_topc @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ X1 @ X2 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['267','316'])).

thf('318',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( m1_pre_topc @ sk_B @ X2 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X2 )
        | ~ ( v2_pre_topc @ X2 )
        | ( v2_struct_0 @ X2 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['257','318'])).

thf('320',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['247','320'])).

thf('322',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['321'])).

thf('323',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['237','322'])).

thf('324',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['227','324'])).

thf('326',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['325','326','327','328'])).

thf('330',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['329'])).

thf('331',plain,
    ( ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['226','330'])).

thf('332',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['331'])).

thf('333',plain,
    ( ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['225','332'])).

thf('334',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['333'])).

thf('335',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('336',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('337',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['228','236'])).

thf('339',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['238','246'])).

thf('340',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['248','256'])).

thf('341',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['258','266'])).

thf('342',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['268','276'])).

thf('343',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['278','286'])).

thf('344',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['288','296'])).

thf('345',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['298','306'])).

thf('346',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X4 @ X7 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X7 @ X5 @ X4 @ X6 @ X3 @ X8 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X7 @ X4 @ X6 ) ) @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('347',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['347'])).

thf('349',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['344','348'])).

thf('350',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['349'])).

thf('351',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['343','350'])).

thf('352',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['351'])).

thf('353',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['342','352'])).

thf('354',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['353'])).

thf('355',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['341','354'])).

thf('356',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['355'])).

thf('357',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['340','356'])).

thf('358',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['339','358'])).

thf('360',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['359'])).

thf('361',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['338','360'])).

thf('362',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['361'])).

thf('363',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['337','362'])).

thf('364',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('367',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['363','364','365','366'])).

thf('368',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['367'])).

thf('369',plain,
    ( ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['336','368'])).

thf('370',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['369'])).

thf('371',plain,
    ( ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['335','370'])).

thf('372',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['371'])).

thf('373',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('374',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('375',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['228','236'])).

thf('377',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['238','246'])).

thf('378',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['248','256'])).

thf('379',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['258','266'])).

thf('380',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['268','276'])).

thf('381',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['278','286'])).

thf('382',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['288','296'])).

thf('383',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['298','306'])).

thf('384',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_pre_topc @ X4 @ X7 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X7 @ X5 @ X4 @ X6 @ X3 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X7 @ X4 @ X6 ) ) @ ( u1_struct_0 @ X5 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('385',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_B )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['383','384'])).

thf('386',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['385'])).

thf('387',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['382','386'])).

thf('388',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['387'])).

thf('389',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['381','388'])).

thf('390',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['389'])).

thf('391',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['380','390'])).

thf('392',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['391'])).

thf('393',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X2 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ~ ( l1_pre_topc @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ X0 @ X1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['379','392'])).

thf('394',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( m1_pre_topc @ X0 @ X1 )
        | ( v2_struct_0 @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X1 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X1 )
        | ~ ( v2_pre_topc @ X1 )
        | ( v2_struct_0 @ X1 )
        | ~ ( v1_funct_1 @ X2 )
        | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['393'])).

thf('395',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['378','394'])).

thf('396',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['395'])).

thf('397',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['377','396'])).

thf('398',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['397'])).

thf('399',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['376','398'])).

thf('400',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_B @ X0 )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 )
        | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['399'])).

thf('401',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['375','400'])).

thf('402',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('403',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('404',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['401','402','403','404'])).

thf('406',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['405'])).

thf('407',plain,
    ( ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['374','406'])).

thf('408',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['407'])).

thf('409',plain,
    ( ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['373','408'])).

thf('410',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['409'])).

thf('411',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['209','217'])).

thf('412',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['268','276'])).

thf('413',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['258','266'])).

thf('414',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('415',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('416',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('417',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( v1_funct_2 @ ( sk_E @ X23 @ X21 @ X22 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) ) @ ( u1_struct_0 @ ( sk_D @ X23 @ X21 @ X22 ) ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('419',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_2 @ ( sk_E @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['417','418'])).

thf('420',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('421',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('422',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v1_funct_2 @ ( sk_E @ X0 @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['419','420','421'])).

thf('423',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['416','422'])).

thf('424',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['415','423'])).

thf('425',plain,
    ( ( ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['414','424'])).

thf('426',plain,
    ( ( ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['425'])).

thf('427',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('428',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('429',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('431',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( m1_subset_1 @ ( sk_E @ X23 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) ) @ ( u1_struct_0 @ ( sk_D @ X23 @ X21 @ X22 ) ) ) ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('432',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['430','431'])).

thf('433',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('435',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) ) @ ( u1_struct_0 @ ( sk_D @ X0 @ sk_C @ sk_A ) ) ) ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['432','433','434'])).

thf('436',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['429','435'])).

thf('437',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['428','436'])).

thf('438',plain,
    ( ( ( m1_subset_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['427','437'])).

thf('439',plain,
    ( ( ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['438'])).

thf(t138_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ E @ ( k10_tmap_1 @ A @ B @ C @ D @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) ) ) ) ) ) ) )).

thf('440',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ X28 @ X29 @ X27 ) ) @ ( u1_struct_0 @ X26 ) @ X30 @ ( k10_tmap_1 @ X28 @ X26 @ X29 @ X27 @ ( k3_tmap_1 @ X28 @ X26 @ ( k1_tsep_1 @ X28 @ X29 @ X27 ) @ X29 @ X30 ) @ ( k3_tmap_1 @ X28 @ X26 @ ( k1_tsep_1 @ X28 @ X29 @ X27 ) @ X27 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X28 @ X29 @ X27 ) ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ ( k1_tsep_1 @ X28 @ X29 @ X27 ) ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t138_tmap_1])).

thf('441',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['439','440'])).

thf('442',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('443',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('445',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('446',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['441','442','443','444','445'])).

thf('447',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['446'])).

thf('448',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['426','447'])).

thf('449',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['448'])).

thf('450',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['413','449'])).

thf('451',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['450'])).

thf('452',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['412','451'])).

thf('453',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['452'])).

thf('454',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['411','453'])).

thf('455',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['454'])).

thf('456',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['209','217'])).

thf('457',plain,
    ( ( ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['425'])).

thf('458',plain,
    ( ( ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['438'])).

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

thf('459',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_funct_2 @ X13 @ X14 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('460',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ X0 )
        | ( ( sk_E @ sk_B @ sk_C @ sk_A )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['458','459'])).

thf('461',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( ( sk_E @ sk_B @ sk_C @ sk_A )
          = X0 )
        | ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ X0 )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['457','460'])).

thf('462',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ X0 )
        | ( ( sk_E @ sk_B @ sk_C @ sk_A )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['461'])).

thf('463',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( ( sk_E @ sk_B @ sk_C @ sk_A )
          = X0 )
        | ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['456','462'])).

thf('464',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ X0 )
        | ( ( sk_E @ sk_B @ sk_C @ sk_A )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['463'])).

thf('465',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['455','464'])).

thf('466',plain,
    ( ( ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['465'])).

thf('467',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['410','466'])).

thf('468',plain,
    ( ( ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['467'])).

thf('469',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['372','468'])).

thf('470',plain,
    ( ( ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['469'])).

thf('471',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['334','470'])).

thf('472',plain,
    ( ( ( ( sk_E @ sk_B @ sk_C @ sk_A )
        = ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['471'])).

thf('473',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('474',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('475',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['278','286'])).

thf('476',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('477',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('478',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('479',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X22 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ X23 @ ( sk_E @ X23 @ X21 @ X22 ) ) @ X23 @ ( sk_D @ X23 @ X21 @ X22 ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('480',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['478','479'])).

thf('481',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('482',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('483',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ X0 @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ X0 @ ( sk_D @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['480','481','482'])).

thf('484',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['477','483'])).

thf('485',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['476','484'])).

thf('486',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['288','296'])).

thf('487',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['298','306'])).

thf('488',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['258','266'])).

thf('489',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['268','276'])).

thf('490',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['228','236'])).

thf('491',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('492',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('493',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('494',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X22 @ ( sk_D @ X23 @ X21 @ X22 ) @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ X21 @ ( sk_E @ X23 @ X21 @ X22 ) ) @ X21 @ ( sk_D @ X23 @ X21 @ X22 ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('495',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['493','494'])).

thf('496',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('497',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('498',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ X0 @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ X0 ) @ sk_C @ ( sk_E @ X0 @ sk_C @ sk_A ) ) @ sk_C @ ( sk_D @ X0 @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['495','496','497'])).

thf('499',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( r1_tsep_1 @ sk_C @ sk_B )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
    | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['492','498'])).

thf('500',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['491','499'])).

thf('501',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['238','246'])).

thf('502',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['248','256'])).

thf('503',plain,
    ( ! [X40: $i,X41: $i,X42: $i] :
        ( ( v2_struct_0 @ X40 )
        | ~ ( v2_pre_topc @ X40 )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v1_funct_1 @ X41 )
        | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
        | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
        | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
        | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
        | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
        | ~ ( v1_funct_1 @ X42 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) )
   <= ! [X40: $i,X41: $i,X42: $i] :
        ( ( v2_struct_0 @ X40 )
        | ~ ( v2_pre_topc @ X40 )
        | ~ ( l1_pre_topc @ X40 )
        | ~ ( v1_funct_1 @ X41 )
        | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
        | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
        | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
        | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
        | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
        | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
        | ~ ( v1_funct_1 @ X42 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ),
    inference(split,[status(esa)],['190'])).

thf('504',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['502','503'])).

thf('505',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['501','504'])).

thf('506',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_C @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['505'])).

thf('507',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['500','506'])).

thf('508',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['507'])).

thf('509',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['490','508'])).

thf('510',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( l1_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['509'])).

thf('511',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['489','510'])).

thf('512',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v2_pre_topc @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['511'])).

thf('513',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['488','512'])).

thf('514',plain,
    ( ! [X0: $i] :
        ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ X0 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
        | ~ ( v5_pre_topc @ X0 @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_B )
        | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
        | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['513'])).

thf('515',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['487','514'])).

thf('516',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['515'])).

thf('517',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['486','516'])).

thf('518',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ sk_B @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['517'])).

thf('519',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['485','518'])).

thf('520',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['519'])).

thf('521',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['475','520'])).

thf('522',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['521'])).

thf('523',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup+',[status(thm)],['474','522'])).

thf('524',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['523'])).

thf('525',plain,
    ( ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup+',[status(thm)],['473','524'])).

thf('526',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B @ sk_C @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) @ ( k3_tmap_1 @ sk_A @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['525'])).

thf('527',plain,
    ( ( ( v5_pre_topc @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup+',[status(thm)],['472','526'])).

thf('528',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v5_pre_topc @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['527'])).

thf('529',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_A @ sk_C @ sk_B )
      = ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','224'])).

thf('530',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['415','423'])).

thf('531',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['428','436'])).

thf('532',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ~ ( v1_funct_1 @ ( sk_E @ X23 @ X21 @ X22 ) )
      | ~ ( v1_funct_2 @ ( sk_E @ X23 @ X21 @ X22 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) ) @ ( u1_struct_0 @ ( sk_D @ X23 @ X21 @ X22 ) ) )
      | ~ ( v5_pre_topc @ ( sk_E @ X23 @ X21 @ X22 ) @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ ( sk_D @ X23 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ ( sk_E @ X23 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) ) @ ( u1_struct_0 @ ( sk_D @ X23 @ X21 @ X22 ) ) ) ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('533',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ~ ( r1_tsep_1 @ sk_C @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['531','532'])).

thf('534',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('535',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('536',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('537',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('538',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('539',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['533','534','535','536','537','538'])).

thf('540',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_2 @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) ) @ ( u1_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['539'])).

thf('541',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['530','540'])).

thf('542',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['541'])).

thf('543',plain,
    ( ( ~ ( v5_pre_topc @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['529','542'])).

thf('544',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ ( sk_E @ sk_B @ sk_C @ sk_A ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['543'])).

thf('545',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['528','544'])).

thf('546',plain,
    ( ( ~ ( v1_funct_1 @ ( sk_E @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['545'])).

thf('547',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['218','546'])).

thf('548',plain,
    ( ( ( v2_struct_0 @ ( sk_D @ sk_B @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['547'])).

thf('549',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( r1_tsep_1 @ X21 @ X23 )
      | ~ ( v2_struct_0 @ ( sk_D @ X23 @ X21 @ X22 ) )
      | ( r3_tsep_1 @ X22 @ X21 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t135_tmap_1])).

thf('550',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ~ ( r1_tsep_1 @ sk_C @ sk_B )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['548','549'])).

thf('551',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('552',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('553',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('554',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['194','201','208'])).

thf('555',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('556',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(demod,[status(thm)],['550','551','552','553','554','555'])).

thf('557',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r3_tsep_1 @ sk_A @ sk_C @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(simplify,[status(thm)],['556'])).

thf(symmetry_r3_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A )
        & ( m1_pre_topc @ C @ A ) )
     => ( ( r3_tsep_1 @ A @ B @ C )
       => ( r3_tsep_1 @ A @ C @ B ) ) ) )).

thf('558',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( r3_tsep_1 @ X19 @ X20 @ X18 )
      | ~ ( r3_tsep_1 @ X19 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r3_tsep_1])).

thf('559',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ sk_A ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['557','558'])).

thf('560',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('561',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('562',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('563',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(demod,[status(thm)],['559','560','561','562'])).

thf('564',plain,
    ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('565',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference('sup-',[status(thm)],['563','564'])).

thf('566',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('567',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(clc,[status(thm)],['565','566'])).

thf('568',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('569',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( ~ ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
      & ( r1_tsep_1 @ sk_B @ sk_C )
      & ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) ) ) ),
    inference(clc,[status(thm)],['567','568'])).

thf('570',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('571',plain,
    ( ~ ! [X40: $i,X41: $i,X42: $i] :
          ( ( v2_struct_0 @ X40 )
          | ~ ( v2_pre_topc @ X40 )
          | ~ ( l1_pre_topc @ X40 )
          | ~ ( v1_funct_1 @ X41 )
          | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v5_pre_topc @ X41 @ sk_C @ X40 )
          | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) ) ) )
          | ~ ( v5_pre_topc @ X42 @ sk_B @ X40 )
          | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X40 ) )
          | ~ ( v1_funct_1 @ X42 )
          | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X40 @ sk_B @ sk_C @ X42 @ X41 ) @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X40 ) )
    | ( r3_tsep_1 @ sk_A @ sk_B @ sk_C )
    | ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['569','570'])).

thf('572',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['42','75','108','167','168','169','170','171','172','173','174','175','176','177','178','179','188','189','191','571'])).


%------------------------------------------------------------------------------
