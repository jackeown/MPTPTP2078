%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O9NmfztF9H

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:15 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 515 expanded)
%              Number of leaves         :   26 ( 164 expanded)
%              Depth                    :   23
%              Number of atoms          : 3969 (47345 expanded)
%              Number of equality atoms :   29 ( 302 expanded)
%              Maximal formula depth    :   31 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t153_tmap_1,conjecture,(
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
                & ( v1_tsep_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_tsep_1 @ D @ A )
                    & ( m1_pre_topc @ D @ A ) )
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
                         => ( ( ( A
                                = ( k1_tsep_1 @ A @ C @ D ) )
                              & ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ E )
                              & ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ F ) )
                           => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                              & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ A @ B )
                              & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( v1_tsep_1 @ C @ A )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_tsep_1 @ D @ A )
                      & ( m1_pre_topc @ D @ A ) )
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
                           => ( ( ( A
                                  = ( k1_tsep_1 @ A @ C @ D ) )
                                & ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ E )
                                & ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ F ) )
                             => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ A @ B )
                                & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t153_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_E ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t151_tmap_1,axiom,(
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
                 => ( ( A
                      = ( k1_tsep_1 @ A @ C @ D ) )
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
                           => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ E )
                                & ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ F )
                                & ( r4_tsep_1 @ A @ C @ D ) )
                             => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ A @ B )
                                & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) ) @ X3 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) ) @ X5 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X5 @ X4 @ X0 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X4 @ X1 ) )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t151_tmap_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_tsep_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_tsep_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_tsep_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( r4_tsep_1 @ A @ B @ C ) ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_tsep_1 @ X6 @ X7 )
      | ~ ( m1_pre_topc @ X6 @ X7 )
      | ( r4_tsep_1 @ X7 @ X6 @ X8 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( v1_tsep_1 @ X8 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t88_tsep_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_tsep_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_A != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_F @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','31','32','33','34','35','36','37','38','39','40','41'])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_E ),
    inference(demod,[status(thm)],['1','2'])).

thf('46',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) ) @ X3 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) ) @ X5 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X5 @ X4 @ X0 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X4 @ X1 ) )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t151_tmap_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_A != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['21','22'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_F @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','58'])).

thf('60',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F ),
    inference(demod,[status(thm)],['29','30'])).

thf('61',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64','65','66','67','68','69','70'])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_E ),
    inference(demod,[status(thm)],['1','2'])).

thf('83',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) @ X2 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) ) @ X3 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) ) @ X5 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X5 @ X4 @ X0 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X4 @ X1 ) )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t151_tmap_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ sk_A @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_A != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ sk_A @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ sk_A @ X2 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['21','22'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ sk_A @ X2 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_F @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','95'])).

thf('97',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F ),
    inference(demod,[status(thm)],['29','30'])).

thf('98',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97','98','99','100','101','102','103','104','105','106','107'])).

thf('109',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['43'])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_E ),
    inference(demod,[status(thm)],['1','2'])).

thf('120',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X3 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X0 ) @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X1 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) ) @ X3 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) @ ( k3_tmap_1 @ X2 @ X0 @ ( k1_tsep_1 @ X2 @ X4 @ X1 ) @ X4 @ ( k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3 ) ) @ X5 )
      | ~ ( r4_tsep_1 @ X2 @ X4 @ X1 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ X5 @ X4 @ X0 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ( X2
       != ( k1_tsep_1 @ X2 @ X4 @ X1 ) )
      | ~ ( m1_pre_topc @ X4 @ X2 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t151_tmap_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( sk_A
       != ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['21','22'])).

thf('128',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( sk_A != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v5_pre_topc @ X0 @ sk_D @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v5_pre_topc @ X1 @ sk_C @ X2 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_F @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['119','131'])).

thf('133',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F ),
    inference(demod,[status(thm)],['29','30'])).

thf('134',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','138','139','140','141','142','143'])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['43'])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('156',plain,(
    ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['81','118','154','155'])).

thf('157',plain,(
    ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['44','156'])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    $false ),
    inference(demod,[status(thm)],['0','164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O9NmfztF9H
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:01:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 58 iterations in 0.064s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.38/0.55  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.55  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.38/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.55  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.38/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.55  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.55  thf(t153_tmap_1, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.55             ( l1_pre_topc @ B ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_tsep_1 @ C @ A ) & 
% 0.38/0.55                 ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.55               ( ![D:$i]:
% 0.38/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.38/0.55                     ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.55                   ( ![E:$i]:
% 0.38/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.55                         ( v1_funct_2 @
% 0.38/0.55                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                         ( v5_pre_topc @ E @ C @ B ) & 
% 0.38/0.55                         ( m1_subset_1 @
% 0.38/0.55                           E @ 
% 0.38/0.55                           ( k1_zfmisc_1 @
% 0.38/0.55                             ( k2_zfmisc_1 @
% 0.38/0.55                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.55                       ( ![F:$i]:
% 0.38/0.55                         ( ( ( v1_funct_1 @ F ) & 
% 0.38/0.55                             ( v1_funct_2 @
% 0.38/0.55                               F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                             ( v5_pre_topc @ F @ D @ B ) & 
% 0.38/0.55                             ( m1_subset_1 @
% 0.38/0.55                               F @ 
% 0.38/0.55                               ( k1_zfmisc_1 @
% 0.38/0.55                                 ( k2_zfmisc_1 @
% 0.38/0.55                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.55                           ( ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) & 
% 0.38/0.55                               ( r2_funct_2 @
% 0.38/0.55                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.55                                 ( k3_tmap_1 @
% 0.38/0.55                                   A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.38/0.55                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.38/0.55                                 E ) & 
% 0.38/0.55                               ( r2_funct_2 @
% 0.38/0.55                                 ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.55                                 ( k3_tmap_1 @
% 0.38/0.55                                   A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.38/0.55                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.38/0.55                                 F ) ) =>
% 0.38/0.55                             ( ( v1_funct_1 @
% 0.38/0.55                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.38/0.55                               ( v1_funct_2 @
% 0.38/0.55                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.55                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                               ( v5_pre_topc @
% 0.38/0.55                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ A @ B ) & 
% 0.38/0.55                               ( m1_subset_1 @
% 0.38/0.55                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.55                                 ( k1_zfmisc_1 @
% 0.38/0.55                                   ( k2_zfmisc_1 @
% 0.38/0.55                                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.55            ( l1_pre_topc @ A ) ) =>
% 0.38/0.55          ( ![B:$i]:
% 0.38/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.55                ( l1_pre_topc @ B ) ) =>
% 0.38/0.55              ( ![C:$i]:
% 0.38/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_tsep_1 @ C @ A ) & 
% 0.38/0.55                    ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.55                  ( ![D:$i]:
% 0.38/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.38/0.55                        ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.55                      ( ![E:$i]:
% 0.38/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.55                            ( v1_funct_2 @
% 0.38/0.55                              E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                            ( v5_pre_topc @ E @ C @ B ) & 
% 0.38/0.55                            ( m1_subset_1 @
% 0.38/0.55                              E @ 
% 0.38/0.55                              ( k1_zfmisc_1 @
% 0.38/0.55                                ( k2_zfmisc_1 @
% 0.38/0.55                                  ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.55                          ( ![F:$i]:
% 0.38/0.55                            ( ( ( v1_funct_1 @ F ) & 
% 0.38/0.55                                ( v1_funct_2 @
% 0.38/0.55                                  F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                                ( v5_pre_topc @ F @ D @ B ) & 
% 0.38/0.55                                ( m1_subset_1 @
% 0.38/0.55                                  F @ 
% 0.38/0.55                                  ( k1_zfmisc_1 @
% 0.38/0.55                                    ( k2_zfmisc_1 @
% 0.38/0.55                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.55                              ( ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) & 
% 0.38/0.55                                  ( r2_funct_2 @
% 0.38/0.55                                    ( u1_struct_0 @ C ) @ 
% 0.38/0.55                                    ( u1_struct_0 @ B ) @ 
% 0.38/0.55                                    ( k3_tmap_1 @
% 0.38/0.55                                      A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.38/0.55                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.38/0.55                                    E ) & 
% 0.38/0.55                                  ( r2_funct_2 @
% 0.38/0.55                                    ( u1_struct_0 @ D ) @ 
% 0.38/0.55                                    ( u1_struct_0 @ B ) @ 
% 0.38/0.55                                    ( k3_tmap_1 @
% 0.38/0.55                                      A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.38/0.55                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.38/0.55                                    F ) ) =>
% 0.38/0.55                                ( ( v1_funct_1 @
% 0.38/0.55                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.38/0.55                                  ( v1_funct_2 @
% 0.38/0.55                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.55                                    ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                                  ( v5_pre_topc @
% 0.38/0.55                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.55                                    A @ B ) & 
% 0.38/0.55                                  ( m1_subset_1 @
% 0.38/0.55                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.55                                    ( k1_zfmisc_1 @
% 0.38/0.55                                      ( k2_zfmisc_1 @
% 0.38/0.55                                        ( u1_struct_0 @ A ) @ 
% 0.38/0.55                                        ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t153_tmap_1])).
% 0.38/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_E)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('2', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_E)),
% 0.38/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf('4', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t151_tmap_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.55             ( l1_pre_topc @ B ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.55               ( ![D:$i]:
% 0.38/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.55                   ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 0.38/0.55                     ( ![E:$i]:
% 0.38/0.55                       ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.55                           ( v1_funct_2 @
% 0.38/0.55                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.38/0.55                           ( m1_subset_1 @
% 0.38/0.55                             E @ 
% 0.38/0.55                             ( k1_zfmisc_1 @
% 0.38/0.55                               ( k2_zfmisc_1 @
% 0.38/0.55                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.55                         ( ![F:$i]:
% 0.38/0.55                           ( ( ( v1_funct_1 @ F ) & 
% 0.38/0.55                               ( v1_funct_2 @
% 0.38/0.55                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.38/0.55                               ( m1_subset_1 @
% 0.38/0.55                                 F @ 
% 0.38/0.55                                 ( k1_zfmisc_1 @
% 0.38/0.55                                   ( k2_zfmisc_1 @
% 0.38/0.55                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.55                             ( ( ( r2_funct_2 @
% 0.38/0.55                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.55                                   ( k3_tmap_1 @
% 0.38/0.55                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.38/0.55                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.38/0.55                                   E ) & 
% 0.38/0.55                                 ( r2_funct_2 @
% 0.38/0.55                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.55                                   ( k3_tmap_1 @
% 0.38/0.55                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.38/0.55                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.38/0.55                                   F ) & 
% 0.38/0.55                                 ( r4_tsep_1 @ A @ C @ D ) ) =>
% 0.38/0.55                               ( ( v1_funct_1 @
% 0.38/0.55                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.38/0.55                                 ( v1_funct_2 @
% 0.38/0.55                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.55                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.55                                 ( v5_pre_topc @
% 0.38/0.55                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.55                                   A @ B ) & 
% 0.38/0.55                                 ( m1_subset_1 @
% 0.38/0.55                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.55                                   ( k1_zfmisc_1 @
% 0.38/0.55                                     ( k2_zfmisc_1 @
% 0.38/0.55                                       ( u1_struct_0 @ A ) @ 
% 0.38/0.55                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X1)
% 0.38/0.55          | ~ (m1_pre_topc @ X1 @ X2)
% 0.38/0.55          | ~ (v1_funct_1 @ X3)
% 0.38/0.55          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v5_pre_topc @ X3 @ X1 @ X0)
% 0.38/0.55          | ~ (m1_subset_1 @ X3 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.38/0.55          | (v1_funct_2 @ (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3) @ 
% 0.38/0.55             (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ 
% 0.38/0.55                (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3)) @ 
% 0.38/0.55               X3)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ 
% 0.38/0.55                (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3)) @ 
% 0.38/0.55               X5)
% 0.38/0.55          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.38/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v5_pre_topc @ X5 @ X4 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_funct_1 @ X5)
% 0.38/0.55          | ((X2) != (k1_tsep_1 @ X2 @ X4 @ X1))
% 0.38/0.55          | ~ (m1_pre_topc @ X4 @ X2)
% 0.38/0.55          | (v2_struct_0 @ X4)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [t151_tmap_1])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.55          | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_C @ sk_D))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.55                sk_C @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | (v1_funct_2 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('9', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('10', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('11', plain, ((v1_tsep_1 @ sk_D @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('12', plain, ((v1_tsep_1 @ sk_C @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t88_tsep_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.55           ( ![C:$i]:
% 0.38/0.55             ( ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.55               ( r4_tsep_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.55         (~ (v1_tsep_1 @ X6 @ X7)
% 0.38/0.55          | ~ (m1_pre_topc @ X6 @ X7)
% 0.38/0.55          | (r4_tsep_1 @ X7 @ X6 @ X8)
% 0.38/0.55          | ~ (m1_pre_topc @ X8 @ X7)
% 0.38/0.55          | ~ (v1_tsep_1 @ X8 @ X7)
% 0.38/0.55          | ~ (l1_pre_topc @ X7)
% 0.38/0.55          | ~ (v2_pre_topc @ X7)
% 0.38/0.55          | (v2_struct_0 @ X7))),
% 0.38/0.55      inference('cnf', [status(esa)], [t88_tsep_1])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.38/0.55          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.55          | (r4_tsep_1 @ sk_A @ sk_C @ X0)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.55  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.38/0.55          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.55          | (r4_tsep_1 @ sk_A @ sk_C @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (((r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.55        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['11', '18'])).
% 0.38/0.55  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('21', plain, (((r4_tsep_1 @ sk_A @ sk_C @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.55  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('23', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.38/0.55      inference('clc', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('24', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ((sk_A) != (sk_A))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | (v1_funct_2 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['6', '7', '8', '9', '10', '23', '24', '25'])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | (v1_funct_2 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.38/0.55            (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55           sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_E)
% 0.38/0.55        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.38/0.55        | ~ (m1_subset_1 @ sk_E @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | (v1_funct_2 @ 
% 0.38/0.55           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (m1_subset_1 @ sk_F @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.38/0.55        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (v1_funct_1 @ sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_D)
% 0.38/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['3', '27'])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_F)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('30', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_F)),
% 0.38/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('32', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('34', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_E @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_F @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('37', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('39', plain, ((v1_funct_1 @ sk_F)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (v1_funct_2 @ 
% 0.38/0.55           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | (v2_struct_0 @ sk_D)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['28', '31', '32', '33', '34', '35', '36', '37', '38', '39', 
% 0.38/0.55                 '40', '41'])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.38/0.55        | ~ (v1_funct_2 @ 
% 0.38/0.55             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (v5_pre_topc @ 
% 0.38/0.55             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.38/0.55             sk_B)
% 0.38/0.55        | ~ (m1_subset_1 @ 
% 0.38/0.55             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('44', plain,
% 0.38/0.55      ((~ (v1_funct_2 @ 
% 0.38/0.55           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v1_funct_2 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('split', [status(esa)], ['43'])).
% 0.38/0.55  thf('45', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_E)),
% 0.38/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf('46', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('47', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X1)
% 0.38/0.55          | ~ (m1_pre_topc @ X1 @ X2)
% 0.38/0.55          | ~ (v1_funct_1 @ X3)
% 0.38/0.55          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v5_pre_topc @ X3 @ X1 @ X0)
% 0.38/0.55          | ~ (m1_subset_1 @ X3 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.38/0.55          | (m1_subset_1 @ (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3) @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ 
% 0.38/0.55                (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3)) @ 
% 0.38/0.55               X3)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ 
% 0.38/0.55                (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3)) @ 
% 0.38/0.55               X5)
% 0.38/0.55          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.38/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v5_pre_topc @ X5 @ X4 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_funct_1 @ X5)
% 0.38/0.55          | ((X2) != (k1_tsep_1 @ X2 @ X4 @ X1))
% 0.38/0.55          | ~ (m1_pre_topc @ X4 @ X2)
% 0.38/0.55          | (v2_struct_0 @ X4)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [t151_tmap_1])).
% 0.38/0.55  thf('48', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.55          | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_C @ sk_D))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.55                sk_C @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | (m1_subset_1 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.55  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('51', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('52', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('53', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('54', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ((sk_A) != (sk_A))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | (m1_subset_1 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['48', '49', '50', '51', '52', '53', '54'])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | (m1_subset_1 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['55'])).
% 0.38/0.55  thf('57', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.38/0.55      inference('clc', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('58', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | (m1_subset_1 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.38/0.55            (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55           sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_E)
% 0.38/0.55        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.38/0.55        | ~ (m1_subset_1 @ sk_E @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | (m1_subset_1 @ 
% 0.38/0.55           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55           (k1_zfmisc_1 @ 
% 0.38/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | ~ (m1_subset_1 @ sk_F @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.38/0.55        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (v1_funct_1 @ sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_D)
% 0.38/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['45', '58'])).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_F)),
% 0.38/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('63', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('64', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_E @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('65', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_F @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('66', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('67', plain,
% 0.38/0.55      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('68', plain, ((v1_funct_1 @ sk_F)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('71', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (m1_subset_1 @ 
% 0.38/0.55           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55           (k1_zfmisc_1 @ 
% 0.38/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | (v2_struct_0 @ sk_D)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['59', '60', '61', '62', '63', '64', '65', '66', '67', '68', 
% 0.38/0.55                 '69', '70'])).
% 0.38/0.55  thf('72', plain,
% 0.38/0.55      ((~ (m1_subset_1 @ 
% 0.38/0.55           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55           (k1_zfmisc_1 @ 
% 0.38/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((m1_subset_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.55      inference('split', [status(esa)], ['43'])).
% 0.38/0.55  thf('73', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_B)
% 0.38/0.55         | (v2_struct_0 @ sk_D)
% 0.38/0.55         | (v2_struct_0 @ sk_C)
% 0.38/0.55         | (v2_struct_0 @ sk_A)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((m1_subset_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.55  thf('74', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('75', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((m1_subset_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.55  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('77', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((m1_subset_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.55      inference('clc', [status(thm)], ['75', '76'])).
% 0.38/0.55  thf('78', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('79', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_C))
% 0.38/0.55         <= (~
% 0.38/0.55             ((m1_subset_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.38/0.55      inference('clc', [status(thm)], ['77', '78'])).
% 0.38/0.55  thf('80', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('81', plain,
% 0.38/0.55      (((m1_subset_1 @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55         (k1_zfmisc_1 @ 
% 0.38/0.55          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.38/0.55  thf('82', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_E)),
% 0.38/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf('83', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('84', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X1)
% 0.38/0.55          | ~ (m1_pre_topc @ X1 @ X2)
% 0.38/0.55          | ~ (v1_funct_1 @ X3)
% 0.38/0.55          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v5_pre_topc @ X3 @ X1 @ X0)
% 0.38/0.55          | ~ (m1_subset_1 @ X3 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.38/0.55          | (v5_pre_topc @ (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3) @ X2 @ X0)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ 
% 0.38/0.55                (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3)) @ 
% 0.38/0.55               X3)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ 
% 0.38/0.55                (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3)) @ 
% 0.38/0.55               X5)
% 0.38/0.55          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.38/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v5_pre_topc @ X5 @ X4 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_funct_1 @ X5)
% 0.38/0.55          | ((X2) != (k1_tsep_1 @ X2 @ X4 @ X1))
% 0.38/0.55          | ~ (m1_pre_topc @ X4 @ X2)
% 0.38/0.55          | (v2_struct_0 @ X4)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [t151_tmap_1])).
% 0.38/0.55  thf('85', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.55          | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_C @ sk_D))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.55                sk_C @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | (v5_pre_topc @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             sk_A @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.55  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('88', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('89', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('90', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('91', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('92', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ((sk_A) != (sk_A))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | (v5_pre_topc @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             sk_A @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['85', '86', '87', '88', '89', '90', '91'])).
% 0.38/0.55  thf('93', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | (v5_pre_topc @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             sk_A @ X2)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['92'])).
% 0.38/0.55  thf('94', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.38/0.55      inference('clc', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('95', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | (v5_pre_topc @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.38/0.55             sk_A @ X2)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.38/0.55  thf('96', plain,
% 0.38/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.38/0.55            (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55           sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_E)
% 0.38/0.55        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.38/0.55        | ~ (m1_subset_1 @ sk_E @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | (v5_pre_topc @ 
% 0.38/0.55           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.38/0.55        | ~ (m1_subset_1 @ sk_F @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.38/0.55        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (v1_funct_1 @ sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_D)
% 0.38/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['82', '95'])).
% 0.38/0.55  thf('97', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_F)),
% 0.38/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('98', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('99', plain,
% 0.38/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('100', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('101', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_E @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('102', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_F @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('103', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('104', plain,
% 0.38/0.55      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('105', plain, ((v1_funct_1 @ sk_F)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('107', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('108', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (v5_pre_topc @ 
% 0.38/0.55           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_D)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['96', '97', '98', '99', '100', '101', '102', '103', '104', 
% 0.38/0.55                 '105', '106', '107'])).
% 0.38/0.55  thf('109', plain,
% 0.38/0.55      ((~ (v5_pre_topc @ 
% 0.38/0.55           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v5_pre_topc @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.38/0.55               sk_B)))),
% 0.38/0.55      inference('split', [status(esa)], ['43'])).
% 0.38/0.55  thf('110', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_B)
% 0.38/0.55         | (v2_struct_0 @ sk_D)
% 0.38/0.55         | (v2_struct_0 @ sk_C)
% 0.38/0.55         | (v2_struct_0 @ sk_A)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v5_pre_topc @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.38/0.55               sk_B)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['108', '109'])).
% 0.38/0.55  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('112', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v5_pre_topc @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.38/0.55               sk_B)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['110', '111'])).
% 0.38/0.55  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('114', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v5_pre_topc @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.38/0.55               sk_B)))),
% 0.38/0.55      inference('clc', [status(thm)], ['112', '113'])).
% 0.38/0.55  thf('115', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('116', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_C))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v5_pre_topc @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.38/0.55               sk_B)))),
% 0.38/0.55      inference('clc', [status(thm)], ['114', '115'])).
% 0.38/0.55  thf('117', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('118', plain,
% 0.38/0.55      (((v5_pre_topc @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['116', '117'])).
% 0.38/0.55  thf('119', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_E)),
% 0.38/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf('120', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('121', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X0)
% 0.38/0.55          | ~ (v2_pre_topc @ X0)
% 0.38/0.55          | ~ (l1_pre_topc @ X0)
% 0.38/0.55          | (v2_struct_0 @ X1)
% 0.38/0.55          | ~ (m1_pre_topc @ X1 @ X2)
% 0.38/0.55          | ~ (v1_funct_1 @ X3)
% 0.38/0.55          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v5_pre_topc @ X3 @ X1 @ X0)
% 0.38/0.55          | ~ (m1_subset_1 @ X3 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0))))
% 0.38/0.55          | (v1_funct_1 @ (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3))
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X1 @ 
% 0.38/0.55                (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3)) @ 
% 0.38/0.55               X3)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0) @ 
% 0.38/0.55               (k3_tmap_1 @ X2 @ X0 @ (k1_tsep_1 @ X2 @ X4 @ X1) @ X4 @ 
% 0.38/0.55                (k10_tmap_1 @ X2 @ X0 @ X4 @ X1 @ X5 @ X3)) @ 
% 0.38/0.55               X5)
% 0.38/0.55          | ~ (r4_tsep_1 @ X2 @ X4 @ X1)
% 0.38/0.55          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))))
% 0.38/0.55          | ~ (v5_pre_topc @ X5 @ X4 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X0))
% 0.38/0.55          | ~ (v1_funct_1 @ X5)
% 0.38/0.55          | ((X2) != (k1_tsep_1 @ X2 @ X4 @ X1))
% 0.38/0.55          | ~ (m1_pre_topc @ X4 @ X2)
% 0.38/0.55          | (v2_struct_0 @ X4)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [t151_tmap_1])).
% 0.38/0.55  thf('122', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.55          | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_C @ sk_D))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.55                sk_C @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | (v1_funct_1 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('sup-', [status(thm)], ['120', '121'])).
% 0.38/0.55  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('125', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('126', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('127', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.38/0.55      inference('clc', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('128', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('129', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('130', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55             X0)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | ((sk_A) != (sk_A))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | (v1_funct_1 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ X2))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['122', '123', '124', '125', '126', '127', '128', '129'])).
% 0.38/0.55  thf('131', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         ((v2_struct_0 @ X2)
% 0.38/0.55          | ~ (v2_pre_topc @ X2)
% 0.38/0.55          | ~ (l1_pre_topc @ X2)
% 0.38/0.55          | (v2_struct_0 @ sk_D)
% 0.38/0.55          | ~ (v1_funct_1 @ X0)
% 0.38/0.55          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | (v1_funct_1 @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0))
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X1)
% 0.38/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.55               (k1_zfmisc_1 @ 
% 0.38/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.38/0.55          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.38/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.38/0.55          | ~ (v1_funct_1 @ X1)
% 0.38/0.55          | (v2_struct_0 @ sk_C)
% 0.38/0.55          | (v2_struct_0 @ sk_A)
% 0.38/0.55          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.38/0.55               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.38/0.55                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.38/0.55               X0))),
% 0.38/0.55      inference('simplify', [status(thm)], ['130'])).
% 0.38/0.55  thf('132', plain,
% 0.38/0.55      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.38/0.55            (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55           sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | ~ (v1_funct_1 @ sk_E)
% 0.38/0.55        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.38/0.55        | ~ (m1_subset_1 @ sk_E @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.38/0.55        | ~ (m1_subset_1 @ sk_F @ 
% 0.38/0.55             (k1_zfmisc_1 @ 
% 0.38/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.55        | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.38/0.55        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.55        | ~ (v1_funct_1 @ sk_F)
% 0.38/0.55        | (v2_struct_0 @ sk_D)
% 0.38/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.55        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['119', '131'])).
% 0.38/0.55  thf('133', plain,
% 0.38/0.55      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.55        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.38/0.55        sk_F)),
% 0.38/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('134', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('135', plain,
% 0.38/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('136', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('137', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_E @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('138', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_F @ 
% 0.38/0.55        (k1_zfmisc_1 @ 
% 0.38/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('139', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('140', plain,
% 0.38/0.55      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('141', plain, ((v1_funct_1 @ sk_F)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('142', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('143', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('144', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_A)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.38/0.55        | (v2_struct_0 @ sk_D)
% 0.38/0.55        | (v2_struct_0 @ sk_B))),
% 0.38/0.55      inference('demod', [status(thm)],
% 0.38/0.55                ['132', '133', '134', '135', '136', '137', '138', '139', 
% 0.38/0.55                 '140', '141', '142', '143'])).
% 0.38/0.55  thf('145', plain,
% 0.38/0.55      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v1_funct_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.55      inference('split', [status(esa)], ['43'])).
% 0.38/0.55  thf('146', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_B)
% 0.38/0.55         | (v2_struct_0 @ sk_D)
% 0.38/0.55         | (v2_struct_0 @ sk_C)
% 0.38/0.55         | (v2_struct_0 @ sk_A)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v1_funct_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['144', '145'])).
% 0.38/0.55  thf('147', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('148', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v1_funct_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['146', '147'])).
% 0.38/0.55  thf('149', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('150', plain,
% 0.38/0.55      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v1_funct_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.55      inference('clc', [status(thm)], ['148', '149'])).
% 0.38/0.55  thf('151', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('152', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_C))
% 0.38/0.55         <= (~
% 0.38/0.55             ((v1_funct_1 @ 
% 0.38/0.55               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.55      inference('clc', [status(thm)], ['150', '151'])).
% 0.38/0.55  thf('153', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('154', plain,
% 0.38/0.55      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['152', '153'])).
% 0.38/0.55  thf('155', plain,
% 0.38/0.55      (~
% 0.38/0.55       ((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))) | 
% 0.38/0.55       ~
% 0.38/0.55       ((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))) | 
% 0.38/0.55       ~
% 0.38/0.55       ((v5_pre_topc @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)) | 
% 0.38/0.55       ~
% 0.38/0.55       ((m1_subset_1 @ 
% 0.38/0.55         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55         (k1_zfmisc_1 @ 
% 0.38/0.55          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.38/0.55      inference('split', [status(esa)], ['43'])).
% 0.38/0.55  thf('156', plain,
% 0.38/0.55      (~
% 0.38/0.55       ((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['81', '118', '154', '155'])).
% 0.38/0.55  thf('157', plain,
% 0.38/0.55      (~ (v1_funct_2 @ 
% 0.38/0.55          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.55          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['44', '156'])).
% 0.38/0.55  thf('158', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_B)
% 0.38/0.55        | (v2_struct_0 @ sk_D)
% 0.38/0.55        | (v2_struct_0 @ sk_C)
% 0.38/0.55        | (v2_struct_0 @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['42', '157'])).
% 0.38/0.55  thf('159', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('160', plain,
% 0.38/0.55      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.38/0.55      inference('sup-', [status(thm)], ['158', '159'])).
% 0.38/0.55  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('162', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.38/0.55      inference('clc', [status(thm)], ['160', '161'])).
% 0.38/0.55  thf('163', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('164', plain, ((v2_struct_0 @ sk_C)),
% 0.38/0.55      inference('clc', [status(thm)], ['162', '163'])).
% 0.38/0.55  thf('165', plain, ($false), inference('demod', [status(thm)], ['0', '164'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
