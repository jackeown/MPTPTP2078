%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yJblCNJLPq

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:13 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 638 expanded)
%              Number of leaves         :   29 ( 197 expanded)
%              Depth                    :   26
%              Number of atoms          : 3799 (57596 expanded)
%              Number of equality atoms :   10 ( 338 expanded)
%              Maximal formula depth    :   32 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t151_tmap_1,conjecture,(
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
                                  & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_E ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t140_tmap_1,axiom,(
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
                 => ( ~ ( r1_tsep_1 @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ E )
                                & ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ F ) )
                            <=> ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ ( k3_tmap_1 @ A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) @ ( k3_tmap_1 @ X8 @ X6 @ ( k1_tsep_1 @ X8 @ X10 @ X7 ) @ X10 @ ( k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9 ) ) @ X11 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) @ ( k3_tmap_1 @ X8 @ X6 @ ( k1_tsep_1 @ X8 @ X10 @ X7 ) @ X7 @ ( k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9 ) ) @ X9 )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ X8 @ X10 @ X7 ) ) @ ( u1_struct_0 @ X6 ) @ ( k3_tmap_1 @ X8 @ X6 @ X10 @ ( k2_tsep_1 @ X8 @ X10 @ X7 ) @ X11 ) @ ( k3_tmap_1 @ X8 @ X6 @ X7 @ ( k2_tsep_1 @ X8 @ X10 @ X7 ) @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ( r1_tsep_1 @ X10 @ X7 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t140_tmap_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_C @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ X0 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ X1 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_C @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ X0 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ X1 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) @ ( k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1 ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['7','8','9','10','11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16','17','18','19','22','23','24','25'])).

thf(t144_tmap_1,axiom,(
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
                 => ( ~ ( r1_tsep_1 @ C @ D )
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
                           => ( ( ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ ( k3_tmap_1 @ A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) )
                                & ( r4_tsep_1 @ A @ C @ D ) )
                             => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                                & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v5_pre_topc @ X15 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X14 @ X12 @ X16 @ X13 @ X17 @ X15 ) @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X12 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) @ ( k3_tmap_1 @ X14 @ X12 @ X16 @ ( k2_tsep_1 @ X14 @ X16 @ X13 ) @ X17 ) @ ( k3_tmap_1 @ X14 @ X12 @ X13 @ ( k2_tsep_1 @ X14 @ X16 @ X13 ) @ X15 ) )
      | ~ ( r4_tsep_1 @ X14 @ X16 @ X13 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v5_pre_topc @ X17 @ X16 @ X12 )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ( r1_tsep_1 @ X16 @ X13 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t144_tmap_1])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_E @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_F @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30','31','32','33','34','35','36','37','38','39','40','41','42','43','44'])).

thf('46',plain,
    ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X4 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X4 @ X1 @ X3 ) ) @ ( u1_struct_0 @ X2 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','62'])).

thf('64',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['47'])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X4 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X4 @ X1 @ X3 ) ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X1 @ sk_C @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','92'])).

thf('94',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['47'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X4 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_tmap_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['109','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['47'])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['47'])).

thf('139',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['78','108','137','138'])).

thf('140',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['48','139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('144',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v5_pre_topc @ X21 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X20 @ X18 @ X22 @ X19 @ X23 @ X21 ) @ ( k1_tsep_1 @ X20 @ X22 @ X19 ) @ X18 )
      | ~ ( r4_tsep_1 @ X20 @ X22 @ X19 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v5_pre_topc @ X23 @ X22 @ X18 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( r1_tsep_1 @ X22 @ X19 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t145_tmap_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( r1_tsep_1 @ X1 @ sk_D )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ X2 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_D )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_B @ X1 @ sk_D @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_D ) @ sk_B )
      | ~ ( v5_pre_topc @ sk_F @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( r1_tsep_1 @ X1 @ sk_D )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ X2 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( r4_tsep_1 @ X0 @ X1 @ sk_D )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_B @ X1 @ sk_D @ X2 @ sk_F ) @ ( k1_tsep_1 @ X0 @ X1 @ sk_D ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) @ sk_B )
      | ~ ( r4_tsep_1 @ X0 @ sk_C @ sk_D )
      | ~ ( v5_pre_topc @ sk_E @ sk_C @ sk_B )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) @ sk_B )
      | ~ ( r4_tsep_1 @ X0 @ sk_C @ sk_D )
      | ~ ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( r4_tsep_1 @ X0 @ sk_C @ sk_D )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['141','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) @ sk_B )
      | ~ ( r4_tsep_1 @ X0 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['1','158'])).

thf('160',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['159','160','161','162','163','164'])).

thf('166',plain,
    ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['48','139'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['0','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yJblCNJLPq
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.73/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.73/0.92  % Solved by: fo/fo7.sh
% 0.73/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.92  % done 379 iterations in 0.471s
% 0.73/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.73/0.92  % SZS output start Refutation
% 0.73/0.92  thf(sk_E_type, type, sk_E: $i).
% 0.73/0.92  thf(sk_F_type, type, sk_F: $i).
% 0.73/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.92  thf(sk_D_type, type, sk_D: $i).
% 0.73/0.92  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.73/0.92  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.73/0.92  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.73/0.92  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.73/0.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.73/0.92  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.73/0.92  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.73/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.73/0.92  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.73/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.73/0.92  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.73/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.73/0.92  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.73/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.73/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.73/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.73/0.92  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.73/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.73/0.92  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.73/0.92  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.73/0.92  thf(t151_tmap_1, conjecture,
% 0.73/0.92    (![A:$i]:
% 0.73/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.73/0.92       ( ![B:$i]:
% 0.73/0.92         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.73/0.92             ( l1_pre_topc @ B ) ) =>
% 0.73/0.92           ( ![C:$i]:
% 0.73/0.92             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.73/0.92               ( ![D:$i]:
% 0.73/0.92                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.73/0.92                   ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 0.73/0.92                     ( ![E:$i]:
% 0.73/0.92                       ( ( ( v1_funct_1 @ E ) & 
% 0.73/0.92                           ( v1_funct_2 @
% 0.73/0.92                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.92                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.73/0.92                           ( m1_subset_1 @
% 0.73/0.92                             E @ 
% 0.73/0.92                             ( k1_zfmisc_1 @
% 0.73/0.92                               ( k2_zfmisc_1 @
% 0.73/0.92                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.92                         ( ![F:$i]:
% 0.73/0.92                           ( ( ( v1_funct_1 @ F ) & 
% 0.73/0.92                               ( v1_funct_2 @
% 0.73/0.92                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.92                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.73/0.92                               ( m1_subset_1 @
% 0.73/0.92                                 F @ 
% 0.73/0.92                                 ( k1_zfmisc_1 @
% 0.73/0.92                                   ( k2_zfmisc_1 @
% 0.73/0.92                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.92                             ( ( ( r2_funct_2 @
% 0.73/0.92                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.73/0.92                                   ( k3_tmap_1 @
% 0.73/0.92                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.73/0.92                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.73/0.92                                   E ) & 
% 0.73/0.92                                 ( r2_funct_2 @
% 0.73/0.92                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.73/0.92                                   ( k3_tmap_1 @
% 0.73/0.92                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.73/0.92                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.73/0.92                                   F ) & 
% 0.73/0.92                                 ( r4_tsep_1 @ A @ C @ D ) ) =>
% 0.73/0.92                               ( ( v1_funct_1 @
% 0.73/0.92                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.73/0.92                                 ( v1_funct_2 @
% 0.73/0.92                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.92                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.92                                 ( v5_pre_topc @
% 0.73/0.92                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.92                                   A @ B ) & 
% 0.73/0.92                                 ( m1_subset_1 @
% 0.73/0.92                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.92                                   ( k1_zfmisc_1 @
% 0.73/0.92                                     ( k2_zfmisc_1 @
% 0.73/0.92                                       ( u1_struct_0 @ A ) @ 
% 0.73/0.92                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.73/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.73/0.92    (~( ![A:$i]:
% 0.73/0.92        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.73/0.92            ( l1_pre_topc @ A ) ) =>
% 0.73/0.92          ( ![B:$i]:
% 0.73/0.92            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.73/0.92                ( l1_pre_topc @ B ) ) =>
% 0.73/0.92              ( ![C:$i]:
% 0.73/0.92                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.73/0.92                  ( ![D:$i]:
% 0.73/0.92                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.73/0.92                      ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 0.73/0.92                        ( ![E:$i]:
% 0.73/0.92                          ( ( ( v1_funct_1 @ E ) & 
% 0.73/0.92                              ( v1_funct_2 @
% 0.73/0.92                                E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.92                              ( v5_pre_topc @ E @ C @ B ) & 
% 0.73/0.92                              ( m1_subset_1 @
% 0.73/0.92                                E @ 
% 0.73/0.92                                ( k1_zfmisc_1 @
% 0.73/0.92                                  ( k2_zfmisc_1 @
% 0.73/0.92                                    ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.92                            ( ![F:$i]:
% 0.73/0.92                              ( ( ( v1_funct_1 @ F ) & 
% 0.73/0.92                                  ( v1_funct_2 @
% 0.73/0.92                                    F @ ( u1_struct_0 @ D ) @ 
% 0.73/0.92                                    ( u1_struct_0 @ B ) ) & 
% 0.73/0.92                                  ( v5_pre_topc @ F @ D @ B ) & 
% 0.73/0.92                                  ( m1_subset_1 @
% 0.73/0.92                                    F @ 
% 0.73/0.92                                    ( k1_zfmisc_1 @
% 0.73/0.92                                      ( k2_zfmisc_1 @
% 0.73/0.92                                        ( u1_struct_0 @ D ) @ 
% 0.73/0.92                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.92                                ( ( ( r2_funct_2 @
% 0.73/0.92                                      ( u1_struct_0 @ C ) @ 
% 0.73/0.92                                      ( u1_struct_0 @ B ) @ 
% 0.73/0.92                                      ( k3_tmap_1 @
% 0.73/0.92                                        A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ 
% 0.73/0.92                                        C @ 
% 0.73/0.92                                        ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.73/0.92                                      E ) & 
% 0.73/0.92                                    ( r2_funct_2 @
% 0.73/0.92                                      ( u1_struct_0 @ D ) @ 
% 0.73/0.92                                      ( u1_struct_0 @ B ) @ 
% 0.73/0.92                                      ( k3_tmap_1 @
% 0.73/0.92                                        A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ 
% 0.73/0.92                                        D @ 
% 0.73/0.92                                        ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.73/0.92                                      F ) & 
% 0.73/0.92                                    ( r4_tsep_1 @ A @ C @ D ) ) =>
% 0.73/0.92                                  ( ( v1_funct_1 @
% 0.73/0.92                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.73/0.92                                    ( v1_funct_2 @
% 0.73/0.92                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.92                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.92                                    ( v5_pre_topc @
% 0.73/0.92                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.92                                      A @ B ) & 
% 0.73/0.92                                    ( m1_subset_1 @
% 0.73/0.92                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.92                                      ( k1_zfmisc_1 @
% 0.73/0.92                                        ( k2_zfmisc_1 @
% 0.73/0.92                                          ( u1_struct_0 @ A ) @ 
% 0.73/0.92                                          ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.73/0.92    inference('cnf.neg', [status(esa)], [t151_tmap_1])).
% 0.73/0.92  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('1', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('2', plain,
% 0.73/0.92      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.73/0.92        (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.73/0.92         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.73/0.92        sk_E)),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('3', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('4', plain,
% 0.73/0.92      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.73/0.92        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ 
% 0.73/0.92         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.73/0.92        sk_E)),
% 0.73/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.73/0.92  thf('5', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf(t140_tmap_1, axiom,
% 0.73/0.92    (![A:$i]:
% 0.73/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.73/0.92       ( ![B:$i]:
% 0.73/0.92         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.73/0.92             ( l1_pre_topc @ B ) ) =>
% 0.73/0.92           ( ![C:$i]:
% 0.73/0.92             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.73/0.92               ( ![D:$i]:
% 0.73/0.92                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.73/0.92                   ( ( ~( r1_tsep_1 @ C @ D ) ) =>
% 0.73/0.92                     ( ![E:$i]:
% 0.73/0.92                       ( ( ( v1_funct_1 @ E ) & 
% 0.73/0.92                           ( v1_funct_2 @
% 0.73/0.92                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.92                           ( m1_subset_1 @
% 0.73/0.92                             E @ 
% 0.73/0.92                             ( k1_zfmisc_1 @
% 0.73/0.92                               ( k2_zfmisc_1 @
% 0.73/0.92                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.92                         ( ![F:$i]:
% 0.73/0.92                           ( ( ( v1_funct_1 @ F ) & 
% 0.73/0.92                               ( v1_funct_2 @
% 0.73/0.92                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.92                               ( m1_subset_1 @
% 0.73/0.92                                 F @ 
% 0.73/0.92                                 ( k1_zfmisc_1 @
% 0.73/0.92                                   ( k2_zfmisc_1 @
% 0.73/0.92                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.92                             ( ( ( r2_funct_2 @
% 0.73/0.92                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.73/0.92                                   ( k3_tmap_1 @
% 0.73/0.92                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.73/0.92                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.73/0.92                                   E ) & 
% 0.73/0.92                                 ( r2_funct_2 @
% 0.73/0.92                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.73/0.92                                   ( k3_tmap_1 @
% 0.73/0.92                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.73/0.92                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.73/0.92                                   F ) ) <=>
% 0.73/0.92                               ( r2_funct_2 @
% 0.73/0.92                                 ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ 
% 0.73/0.92                                 ( u1_struct_0 @ B ) @ 
% 0.73/0.92                                 ( k3_tmap_1 @
% 0.73/0.92                                   A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ 
% 0.73/0.92                                 ( k3_tmap_1 @
% 0.73/0.92                                   A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.73/0.92  thf('6', plain,
% 0.73/0.92      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.73/0.92         ((v2_struct_0 @ X6)
% 0.73/0.92          | ~ (v2_pre_topc @ X6)
% 0.73/0.92          | ~ (l1_pre_topc @ X6)
% 0.73/0.92          | (v2_struct_0 @ X7)
% 0.73/0.92          | ~ (m1_pre_topc @ X7 @ X8)
% 0.73/0.92          | ~ (v1_funct_1 @ X9)
% 0.73/0.92          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 0.73/0.92          | ~ (m1_subset_1 @ X9 @ 
% 0.73/0.92               (k1_zfmisc_1 @ 
% 0.73/0.92                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 0.73/0.92          | ~ (r2_funct_2 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6) @ 
% 0.73/0.92               (k3_tmap_1 @ X8 @ X6 @ (k1_tsep_1 @ X8 @ X10 @ X7) @ X10 @ 
% 0.73/0.92                (k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9)) @ 
% 0.73/0.92               X11)
% 0.73/0.92          | ~ (r2_funct_2 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6) @ 
% 0.73/0.92               (k3_tmap_1 @ X8 @ X6 @ (k1_tsep_1 @ X8 @ X10 @ X7) @ X7 @ 
% 0.73/0.92                (k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9)) @ 
% 0.73/0.92               X9)
% 0.73/0.92          | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ X8 @ X10 @ X7)) @ 
% 0.73/0.92             (u1_struct_0 @ X6) @ 
% 0.73/0.92             (k3_tmap_1 @ X8 @ X6 @ X10 @ (k2_tsep_1 @ X8 @ X10 @ X7) @ X11) @ 
% 0.73/0.92             (k3_tmap_1 @ X8 @ X6 @ X7 @ (k2_tsep_1 @ X8 @ X10 @ X7) @ X9))
% 0.73/0.92          | ~ (m1_subset_1 @ X11 @ 
% 0.73/0.92               (k1_zfmisc_1 @ 
% 0.73/0.92                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))))
% 0.73/0.92          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))
% 0.73/0.92          | ~ (v1_funct_1 @ X11)
% 0.73/0.92          | (r1_tsep_1 @ X10 @ X7)
% 0.73/0.92          | ~ (m1_pre_topc @ X10 @ X8)
% 0.73/0.92          | (v2_struct_0 @ X10)
% 0.73/0.92          | ~ (l1_pre_topc @ X8)
% 0.73/0.92          | ~ (v2_pre_topc @ X8)
% 0.73/0.92          | (v2_struct_0 @ X8))),
% 0.73/0.92      inference('cnf', [status(esa)], [t140_tmap_1])).
% 0.73/0.92  thf('7', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.92         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.73/0.92             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.73/0.92              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1)) @ 
% 0.73/0.92             X0)
% 0.73/0.92          | (v2_struct_0 @ sk_A)
% 0.73/0.92          | ~ (v2_pre_topc @ sk_A)
% 0.73/0.92          | ~ (l1_pre_topc @ sk_A)
% 0.73/0.92          | (v2_struct_0 @ sk_C)
% 0.73/0.92          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.73/0.92          | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.92          | ~ (v1_funct_1 @ X0)
% 0.73/0.92          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.73/0.92          | ~ (m1_subset_1 @ X0 @ 
% 0.73/0.92               (k1_zfmisc_1 @ 
% 0.73/0.92                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.73/0.92          | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.73/0.92             (u1_struct_0 @ X2) @ 
% 0.73/0.92             (k3_tmap_1 @ sk_A @ X2 @ sk_C @ 
% 0.73/0.92              (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ X0) @ 
% 0.73/0.92             (k3_tmap_1 @ sk_A @ X2 @ sk_D @ 
% 0.73/0.92              (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ X1))
% 0.73/0.92          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.73/0.92               (k3_tmap_1 @ sk_A @ X2 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.73/0.92                sk_D @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1)) @ 
% 0.73/0.92               X1)
% 0.73/0.92          | ~ (m1_subset_1 @ X1 @ 
% 0.73/0.92               (k1_zfmisc_1 @ 
% 0.73/0.92                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.73/0.92          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.73/0.92          | ~ (v1_funct_1 @ X1)
% 0.73/0.92          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.73/0.92          | (v2_struct_0 @ sk_D)
% 0.73/0.92          | ~ (l1_pre_topc @ X2)
% 0.73/0.92          | ~ (v2_pre_topc @ X2)
% 0.73/0.92          | (v2_struct_0 @ X2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.73/0.92  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('10', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('11', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('13', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.92         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.73/0.92             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.73/0.92              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1)) @ 
% 0.73/0.92             X0)
% 0.73/0.92          | (v2_struct_0 @ sk_A)
% 0.73/0.92          | (v2_struct_0 @ sk_C)
% 0.73/0.92          | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.92          | ~ (v1_funct_1 @ X0)
% 0.73/0.92          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.73/0.92          | ~ (m1_subset_1 @ X0 @ 
% 0.73/0.92               (k1_zfmisc_1 @ 
% 0.73/0.92                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.73/0.92          | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.73/0.92             (u1_struct_0 @ X2) @ 
% 0.73/0.92             (k3_tmap_1 @ sk_A @ X2 @ sk_C @ 
% 0.73/0.92              (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ X0) @ 
% 0.73/0.92             (k3_tmap_1 @ sk_A @ X2 @ sk_D @ 
% 0.73/0.92              (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ X1))
% 0.73/0.92          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.73/0.92               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.73/0.92                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1)) @ 
% 0.73/0.92               X1)
% 0.73/0.92          | ~ (m1_subset_1 @ X1 @ 
% 0.73/0.92               (k1_zfmisc_1 @ 
% 0.73/0.92                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.73/0.92          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.73/0.92          | ~ (v1_funct_1 @ X1)
% 0.73/0.92          | (v2_struct_0 @ sk_D)
% 0.73/0.92          | ~ (l1_pre_topc @ X2)
% 0.73/0.92          | ~ (v2_pre_topc @ X2)
% 0.73/0.92          | (v2_struct_0 @ X2))),
% 0.73/0.92      inference('demod', [status(thm)], ['7', '8', '9', '10', '11', '12'])).
% 0.73/0.92  thf('14', plain,
% 0.73/0.92      (((v2_struct_0 @ sk_B)
% 0.73/0.92        | ~ (v2_pre_topc @ sk_B)
% 0.73/0.92        | ~ (l1_pre_topc @ sk_B)
% 0.73/0.92        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | ~ (v1_funct_1 @ sk_F)
% 0.73/0.93        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.73/0.93        | ~ (m1_subset_1 @ sk_F @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.73/0.93             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.73/0.93              (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.73/0.93             sk_F)
% 0.73/0.93        | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.73/0.93           (u1_struct_0 @ sk_B) @ 
% 0.73/0.93           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 0.73/0.93            (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_E) @ 
% 0.73/0.93           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ 
% 0.73/0.93            (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_F))
% 0.73/0.93        | ~ (m1_subset_1 @ sk_E @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.73/0.93        | ~ (v1_funct_1 @ sk_E)
% 0.73/0.93        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_A))),
% 0.73/0.93      inference('sup-', [status(thm)], ['4', '13'])).
% 0.73/0.93  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('17', plain, ((v1_funct_1 @ sk_F)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('18', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('19', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_F @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('20', plain,
% 0.73/0.93      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.73/0.93        (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.73/0.93        sk_F)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('21', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('22', plain,
% 0.73/0.93      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.73/0.93        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.73/0.93        sk_F)),
% 0.73/0.93      inference('demod', [status(thm)], ['20', '21'])).
% 0.73/0.93  thf('23', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_E @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('24', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('26', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.73/0.93           (u1_struct_0 @ sk_B) @ 
% 0.73/0.93           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 0.73/0.93            (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_E) @ 
% 0.73/0.93           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ 
% 0.73/0.93            (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_F))
% 0.73/0.93        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_A))),
% 0.73/0.93      inference('demod', [status(thm)],
% 0.73/0.93                ['14', '15', '16', '17', '18', '19', '22', '23', '24', '25'])).
% 0.73/0.93  thf(t144_tmap_1, axiom,
% 0.73/0.93    (![A:$i]:
% 0.73/0.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.73/0.93       ( ![B:$i]:
% 0.73/0.93         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.73/0.93             ( l1_pre_topc @ B ) ) =>
% 0.73/0.93           ( ![C:$i]:
% 0.73/0.93             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.73/0.93               ( ![D:$i]:
% 0.73/0.93                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.73/0.93                   ( ( ~( r1_tsep_1 @ C @ D ) ) =>
% 0.73/0.93                     ( ![E:$i]:
% 0.73/0.93                       ( ( ( v1_funct_1 @ E ) & 
% 0.73/0.93                           ( v1_funct_2 @
% 0.73/0.93                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.93                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.73/0.93                           ( m1_subset_1 @
% 0.73/0.93                             E @ 
% 0.73/0.93                             ( k1_zfmisc_1 @
% 0.73/0.93                               ( k2_zfmisc_1 @
% 0.73/0.93                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.93                         ( ![F:$i]:
% 0.73/0.93                           ( ( ( v1_funct_1 @ F ) & 
% 0.73/0.93                               ( v1_funct_2 @
% 0.73/0.93                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.93                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.73/0.93                               ( m1_subset_1 @
% 0.73/0.93                                 F @ 
% 0.73/0.93                                 ( k1_zfmisc_1 @
% 0.73/0.93                                   ( k2_zfmisc_1 @
% 0.73/0.93                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.93                             ( ( ( r2_funct_2 @
% 0.73/0.93                                   ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ 
% 0.73/0.93                                   ( u1_struct_0 @ B ) @ 
% 0.73/0.93                                   ( k3_tmap_1 @
% 0.73/0.93                                     A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ 
% 0.73/0.93                                   ( k3_tmap_1 @
% 0.73/0.93                                     A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) & 
% 0.73/0.93                                 ( r4_tsep_1 @ A @ C @ D ) ) =>
% 0.73/0.93                               ( ( v1_funct_1 @
% 0.73/0.93                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.73/0.93                                 ( v1_funct_2 @
% 0.73/0.93                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.93                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.73/0.93                                   ( u1_struct_0 @ B ) ) & 
% 0.73/0.93                                 ( v5_pre_topc @
% 0.73/0.93                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.93                                   ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.73/0.93                                 ( m1_subset_1 @
% 0.73/0.93                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.93                                   ( k1_zfmisc_1 @
% 0.73/0.93                                     ( k2_zfmisc_1 @
% 0.73/0.93                                       ( u1_struct_0 @
% 0.73/0.93                                         ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.73/0.93                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.73/0.93  thf('27', plain,
% 0.73/0.93      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.73/0.93         ((v2_struct_0 @ X12)
% 0.73/0.93          | ~ (v2_pre_topc @ X12)
% 0.73/0.93          | ~ (l1_pre_topc @ X12)
% 0.73/0.93          | (v2_struct_0 @ X13)
% 0.73/0.93          | ~ (m1_pre_topc @ X13 @ X14)
% 0.73/0.93          | ~ (v1_funct_1 @ X15)
% 0.73/0.93          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.73/0.93          | ~ (v5_pre_topc @ X15 @ X13 @ X12)
% 0.73/0.93          | ~ (m1_subset_1 @ X15 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))))
% 0.73/0.93          | (v5_pre_topc @ (k10_tmap_1 @ X14 @ X12 @ X16 @ X13 @ X17 @ X15) @ 
% 0.73/0.93             (k1_tsep_1 @ X14 @ X16 @ X13) @ X12)
% 0.73/0.93          | ~ (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ X14 @ X16 @ X13)) @ 
% 0.73/0.93               (u1_struct_0 @ X12) @ 
% 0.73/0.93               (k3_tmap_1 @ X14 @ X12 @ X16 @ (k2_tsep_1 @ X14 @ X16 @ X13) @ 
% 0.73/0.93                X17) @ 
% 0.73/0.93               (k3_tmap_1 @ X14 @ X12 @ X13 @ (k2_tsep_1 @ X14 @ X16 @ X13) @ 
% 0.73/0.93                X15))
% 0.73/0.93          | ~ (r4_tsep_1 @ X14 @ X16 @ X13)
% 0.73/0.93          | ~ (m1_subset_1 @ X17 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X12))))
% 0.73/0.93          | ~ (v5_pre_topc @ X17 @ X16 @ X12)
% 0.73/0.93          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X12))
% 0.73/0.93          | ~ (v1_funct_1 @ X17)
% 0.73/0.93          | (r1_tsep_1 @ X16 @ X13)
% 0.73/0.93          | ~ (m1_pre_topc @ X16 @ X14)
% 0.73/0.93          | (v2_struct_0 @ X16)
% 0.73/0.93          | ~ (l1_pre_topc @ X14)
% 0.73/0.93          | ~ (v2_pre_topc @ X14)
% 0.73/0.93          | (v2_struct_0 @ X14))),
% 0.73/0.93      inference('cnf', [status(esa)], [t144_tmap_1])).
% 0.73/0.93  thf('28', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | ~ (v2_pre_topc @ sk_A)
% 0.73/0.93        | ~ (l1_pre_topc @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.73/0.93        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93        | ~ (v1_funct_1 @ sk_E)
% 0.73/0.93        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.73/0.93        | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.73/0.93        | ~ (m1_subset_1 @ sk_E @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.73/0.93        | (v5_pre_topc @ 
% 0.73/0.93           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.73/0.93        | ~ (m1_subset_1 @ sk_F @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93        | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.73/0.93        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.73/0.93        | ~ (v1_funct_1 @ sk_F)
% 0.73/0.93        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | ~ (l1_pre_topc @ sk_B)
% 0.73/0.93        | ~ (v2_pre_topc @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_B))),
% 0.73/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.73/0.93  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('31', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('32', plain, ((v1_funct_1 @ sk_E)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('33', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('34', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('35', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_E @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('36', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('37', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('38', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_F @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('39', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('40', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('41', plain, ((v1_funct_1 @ sk_F)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('44', plain, ((v2_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('45', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93        | (v5_pre_topc @ 
% 0.73/0.93           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_B))),
% 0.73/0.93      inference('demod', [status(thm)],
% 0.73/0.93                ['28', '29', '30', '31', '32', '33', '34', '35', '36', '37', 
% 0.73/0.93                 '38', '39', '40', '41', '42', '43', '44'])).
% 0.73/0.93  thf('46', plain,
% 0.73/0.93      (((v5_pre_topc @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_A))),
% 0.73/0.93      inference('simplify', [status(thm)], ['45'])).
% 0.73/0.93  thf('47', plain,
% 0.73/0.93      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.73/0.93        | ~ (v1_funct_2 @ 
% 0.73/0.93             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.73/0.93        | ~ (v5_pre_topc @ 
% 0.73/0.93             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.73/0.93             sk_B)
% 0.73/0.93        | ~ (m1_subset_1 @ 
% 0.73/0.93             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('48', plain,
% 0.73/0.93      ((~ (v5_pre_topc @ 
% 0.73/0.93           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v5_pre_topc @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.73/0.93               sk_B)))),
% 0.73/0.93      inference('split', [status(esa)], ['47'])).
% 0.73/0.93  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('50', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_F @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('51', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_E @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf(dt_k10_tmap_1, axiom,
% 0.73/0.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.73/0.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.73/0.93         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.73/0.93         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 0.73/0.93         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.73/0.93         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 0.73/0.93         ( v1_funct_1 @ E ) & 
% 0.73/0.93         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.93         ( m1_subset_1 @
% 0.73/0.93           E @ 
% 0.73/0.93           ( k1_zfmisc_1 @
% 0.73/0.93             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.73/0.93         ( v1_funct_1 @ F ) & 
% 0.73/0.93         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.93         ( m1_subset_1 @
% 0.73/0.93           F @ 
% 0.73/0.93           ( k1_zfmisc_1 @
% 0.73/0.93             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.93       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.73/0.93         ( v1_funct_2 @
% 0.73/0.93           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.93           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.93         ( m1_subset_1 @
% 0.73/0.93           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.93           ( k1_zfmisc_1 @
% 0.73/0.93             ( k2_zfmisc_1 @
% 0.73/0.93               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.73/0.93               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.73/0.93  thf('52', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.73/0.93         (~ (m1_subset_1 @ X0 @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.73/0.93          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.73/0.93          | ~ (v1_funct_1 @ X0)
% 0.73/0.93          | ~ (m1_pre_topc @ X3 @ X4)
% 0.73/0.93          | (v2_struct_0 @ X3)
% 0.73/0.93          | ~ (m1_pre_topc @ X1 @ X4)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (l1_pre_topc @ X2)
% 0.73/0.93          | ~ (v2_pre_topc @ X2)
% 0.73/0.93          | (v2_struct_0 @ X2)
% 0.73/0.93          | ~ (l1_pre_topc @ X4)
% 0.73/0.93          | ~ (v2_pre_topc @ X4)
% 0.73/0.93          | (v2_struct_0 @ X4)
% 0.73/0.93          | ~ (v1_funct_1 @ X5)
% 0.73/0.93          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.73/0.93          | ~ (m1_subset_1 @ X5 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.73/0.93          | (m1_subset_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ 
% 0.73/0.93               (u1_struct_0 @ X2)))))),
% 0.73/0.93      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.73/0.93  thf('53', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.93         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.73/0.93           (k1_zfmisc_1 @ 
% 0.73/0.93            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.73/0.93             (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (m1_subset_1 @ X2 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v1_funct_1 @ X2)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (v2_pre_topc @ X1)
% 0.73/0.93          | ~ (l1_pre_topc @ X1)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | ~ (v2_pre_topc @ sk_B)
% 0.73/0.93          | ~ (l1_pre_topc @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | ~ (m1_pre_topc @ X0 @ X1)
% 0.73/0.93          | ~ (v1_funct_1 @ sk_E)
% 0.73/0.93          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.73/0.93      inference('sup-', [status(thm)], ['51', '52'])).
% 0.73/0.93  thf('54', plain, ((v2_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('56', plain, ((v1_funct_1 @ sk_E)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('57', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('58', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.93         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.73/0.93           (k1_zfmisc_1 @ 
% 0.73/0.93            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.73/0.93             (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (m1_subset_1 @ X2 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v1_funct_1 @ X2)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (v2_pre_topc @ X1)
% 0.73/0.93          | ~ (l1_pre_topc @ X1)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.73/0.93      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.73/0.93  thf('59', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         (~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | ~ (v1_funct_1 @ sk_F)
% 0.73/0.93          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | (m1_subset_1 @ 
% 0.73/0.93             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.73/0.93               (u1_struct_0 @ sk_B)))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['50', '58'])).
% 0.73/0.93  thf('60', plain, ((v1_funct_1 @ sk_F)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('61', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('62', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         (~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | (m1_subset_1 @ 
% 0.73/0.93             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.73/0.93               (u1_struct_0 @ sk_B)))))),
% 0.73/0.93      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.73/0.93  thf('63', plain,
% 0.73/0.93      (((m1_subset_1 @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93         (k1_zfmisc_1 @ 
% 0.73/0.93          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.73/0.93           (u1_struct_0 @ sk_B))))
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | ~ (v2_pre_topc @ sk_A)
% 0.73/0.93        | ~ (l1_pre_topc @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_D))),
% 0.73/0.93      inference('sup-', [status(thm)], ['49', '62'])).
% 0.73/0.93  thf('64', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('67', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('68', plain,
% 0.73/0.93      (((m1_subset_1 @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93         (k1_zfmisc_1 @ 
% 0.73/0.93          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_D))),
% 0.73/0.93      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.73/0.93  thf('69', plain,
% 0.73/0.93      ((~ (m1_subset_1 @ 
% 0.73/0.93           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93           (k1_zfmisc_1 @ 
% 0.73/0.93            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.73/0.93         <= (~
% 0.73/0.93             ((m1_subset_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.73/0.93      inference('split', [status(esa)], ['47'])).
% 0.73/0.93  thf('70', plain,
% 0.73/0.93      ((((v2_struct_0 @ sk_D)
% 0.73/0.93         | (v2_struct_0 @ sk_C)
% 0.73/0.93         | (v2_struct_0 @ sk_B)
% 0.73/0.93         | (v2_struct_0 @ sk_A)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((m1_subset_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['68', '69'])).
% 0.73/0.93  thf('71', plain, (~ (v2_struct_0 @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('72', plain,
% 0.73/0.93      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((m1_subset_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['70', '71'])).
% 0.73/0.93  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('74', plain,
% 0.73/0.93      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((m1_subset_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.73/0.93      inference('clc', [status(thm)], ['72', '73'])).
% 0.73/0.93  thf('75', plain, (~ (v2_struct_0 @ sk_D)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('76', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_C))
% 0.73/0.93         <= (~
% 0.73/0.93             ((m1_subset_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.73/0.93      inference('clc', [status(thm)], ['74', '75'])).
% 0.73/0.93  thf('77', plain, (~ (v2_struct_0 @ sk_C)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('78', plain,
% 0.73/0.93      (((m1_subset_1 @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93         (k1_zfmisc_1 @ 
% 0.73/0.93          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['76', '77'])).
% 0.73/0.93  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('80', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_F @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('81', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_E @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('82', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.73/0.93         (~ (m1_subset_1 @ X0 @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.73/0.93          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.73/0.93          | ~ (v1_funct_1 @ X0)
% 0.73/0.93          | ~ (m1_pre_topc @ X3 @ X4)
% 0.73/0.93          | (v2_struct_0 @ X3)
% 0.73/0.93          | ~ (m1_pre_topc @ X1 @ X4)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (l1_pre_topc @ X2)
% 0.73/0.93          | ~ (v2_pre_topc @ X2)
% 0.73/0.93          | (v2_struct_0 @ X2)
% 0.73/0.93          | ~ (l1_pre_topc @ X4)
% 0.73/0.93          | ~ (v2_pre_topc @ X4)
% 0.73/0.93          | (v2_struct_0 @ X4)
% 0.73/0.93          | ~ (v1_funct_1 @ X5)
% 0.73/0.93          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.73/0.93          | ~ (m1_subset_1 @ X5 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.73/0.93          | (v1_funct_2 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.73/0.93             (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ (u1_struct_0 @ X2)))),
% 0.73/0.93      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.73/0.93  thf('83', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.93         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.73/0.93           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (m1_subset_1 @ X2 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v1_funct_1 @ X2)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (v2_pre_topc @ X1)
% 0.73/0.93          | ~ (l1_pre_topc @ X1)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | ~ (v2_pre_topc @ sk_B)
% 0.73/0.93          | ~ (l1_pre_topc @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | ~ (m1_pre_topc @ X0 @ X1)
% 0.73/0.93          | ~ (v1_funct_1 @ sk_E)
% 0.73/0.93          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.73/0.93      inference('sup-', [status(thm)], ['81', '82'])).
% 0.73/0.93  thf('84', plain, ((v2_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('86', plain, ((v1_funct_1 @ sk_E)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('87', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('88', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.93         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.73/0.93           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (m1_subset_1 @ X2 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v1_funct_1 @ X2)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (v2_pre_topc @ X1)
% 0.73/0.93          | ~ (l1_pre_topc @ X1)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.73/0.93      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 0.73/0.93  thf('89', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         (~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | ~ (v1_funct_1 @ sk_F)
% 0.73/0.93          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | (v1_funct_2 @ 
% 0.73/0.93             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.73/0.93             (u1_struct_0 @ sk_B)))),
% 0.73/0.93      inference('sup-', [status(thm)], ['80', '88'])).
% 0.73/0.93  thf('90', plain, ((v1_funct_1 @ sk_F)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('91', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('92', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         (~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | (v1_funct_2 @ 
% 0.73/0.93             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.73/0.93             (u1_struct_0 @ sk_B)))),
% 0.73/0.93      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.73/0.93  thf('93', plain,
% 0.73/0.93      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.73/0.93         (u1_struct_0 @ sk_B))
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | ~ (v2_pre_topc @ sk_A)
% 0.73/0.93        | ~ (l1_pre_topc @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_D))),
% 0.73/0.93      inference('sup-', [status(thm)], ['79', '92'])).
% 0.73/0.93  thf('94', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('97', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('98', plain,
% 0.73/0.93      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_D))),
% 0.73/0.93      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 0.73/0.93  thf('99', plain,
% 0.73/0.93      ((~ (v1_funct_2 @ 
% 0.73/0.93           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_2 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('split', [status(esa)], ['47'])).
% 0.73/0.93  thf('100', plain,
% 0.73/0.93      ((((v2_struct_0 @ sk_D)
% 0.73/0.93         | (v2_struct_0 @ sk_C)
% 0.73/0.93         | (v2_struct_0 @ sk_B)
% 0.73/0.93         | (v2_struct_0 @ sk_A)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_2 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['98', '99'])).
% 0.73/0.93  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('102', plain,
% 0.73/0.93      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_2 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['100', '101'])).
% 0.73/0.93  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('104', plain,
% 0.73/0.93      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_2 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('clc', [status(thm)], ['102', '103'])).
% 0.73/0.93  thf('105', plain, (~ (v2_struct_0 @ sk_D)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('106', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_C))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_2 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('clc', [status(thm)], ['104', '105'])).
% 0.73/0.93  thf('107', plain, (~ (v2_struct_0 @ sk_C)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('108', plain,
% 0.73/0.93      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.73/0.93      inference('sup-', [status(thm)], ['106', '107'])).
% 0.73/0.93  thf('109', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('110', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_F @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('111', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_E @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('112', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.73/0.93         (~ (m1_subset_1 @ X0 @ 
% 0.73/0.93             (k1_zfmisc_1 @ 
% 0.73/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.73/0.93          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.73/0.93          | ~ (v1_funct_1 @ X0)
% 0.73/0.93          | ~ (m1_pre_topc @ X3 @ X4)
% 0.73/0.93          | (v2_struct_0 @ X3)
% 0.73/0.93          | ~ (m1_pre_topc @ X1 @ X4)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (l1_pre_topc @ X2)
% 0.73/0.93          | ~ (v2_pre_topc @ X2)
% 0.73/0.93          | (v2_struct_0 @ X2)
% 0.73/0.93          | ~ (l1_pre_topc @ X4)
% 0.73/0.93          | ~ (v2_pre_topc @ X4)
% 0.73/0.93          | (v2_struct_0 @ X4)
% 0.73/0.93          | ~ (v1_funct_1 @ X5)
% 0.73/0.93          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.73/0.93          | ~ (m1_subset_1 @ X5 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.73/0.93          | (v1_funct_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5)))),
% 0.73/0.93      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.73/0.93  thf('113', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.93         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.73/0.93          | ~ (m1_subset_1 @ X0 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v1_funct_1 @ X0)
% 0.73/0.93          | (v2_struct_0 @ X2)
% 0.73/0.93          | ~ (v2_pre_topc @ X2)
% 0.73/0.93          | ~ (l1_pre_topc @ X2)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | ~ (v2_pre_topc @ sk_B)
% 0.73/0.93          | ~ (l1_pre_topc @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (m1_pre_topc @ X1 @ X2)
% 0.73/0.93          | ~ (v1_funct_1 @ sk_E)
% 0.73/0.93          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.73/0.93      inference('sup-', [status(thm)], ['111', '112'])).
% 0.73/0.93  thf('114', plain, ((v2_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('115', plain, ((l1_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('116', plain, ((v1_funct_1 @ sk_E)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('117', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('118', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.93         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.73/0.93          | ~ (m1_subset_1 @ X0 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v1_funct_1 @ X0)
% 0.73/0.93          | (v2_struct_0 @ X2)
% 0.73/0.93          | ~ (v2_pre_topc @ X2)
% 0.73/0.93          | ~ (l1_pre_topc @ X2)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (m1_pre_topc @ X1 @ X2))),
% 0.73/0.93      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.73/0.93  thf('119', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         (~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | ~ (v1_funct_1 @ sk_F)
% 0.73/0.93          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.73/0.93      inference('sup-', [status(thm)], ['110', '118'])).
% 0.73/0.93  thf('120', plain, ((v1_funct_1 @ sk_F)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('121', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('122', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         (~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | (v2_struct_0 @ sk_B)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.73/0.93      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.73/0.93  thf('123', plain,
% 0.73/0.93      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | ~ (v2_pre_topc @ sk_A)
% 0.73/0.93        | ~ (l1_pre_topc @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_D))),
% 0.73/0.93      inference('sup-', [status(thm)], ['109', '122'])).
% 0.73/0.93  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('126', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('127', plain,
% 0.73/0.93      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_D))),
% 0.73/0.93      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.73/0.93  thf('128', plain,
% 0.73/0.93      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.73/0.93      inference('split', [status(esa)], ['47'])).
% 0.73/0.93  thf('129', plain,
% 0.73/0.93      ((((v2_struct_0 @ sk_D)
% 0.73/0.93         | (v2_struct_0 @ sk_C)
% 0.73/0.93         | (v2_struct_0 @ sk_B)
% 0.73/0.93         | (v2_struct_0 @ sk_A)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['127', '128'])).
% 0.73/0.93  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('131', plain,
% 0.73/0.93      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['129', '130'])).
% 0.73/0.93  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('133', plain,
% 0.73/0.93      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.73/0.93      inference('clc', [status(thm)], ['131', '132'])).
% 0.73/0.93  thf('134', plain, (~ (v2_struct_0 @ sk_D)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('135', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_C))
% 0.73/0.93         <= (~
% 0.73/0.93             ((v1_funct_1 @ 
% 0.73/0.93               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.73/0.93      inference('clc', [status(thm)], ['133', '134'])).
% 0.73/0.93  thf('136', plain, (~ (v2_struct_0 @ sk_C)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('137', plain,
% 0.73/0.93      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.73/0.93      inference('sup-', [status(thm)], ['135', '136'])).
% 0.73/0.93  thf('138', plain,
% 0.73/0.93      (~
% 0.73/0.93       ((v5_pre_topc @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)) | 
% 0.73/0.93       ~
% 0.73/0.93       ((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))) | 
% 0.73/0.93       ~
% 0.73/0.93       ((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))) | 
% 0.73/0.93       ~
% 0.73/0.93       ((m1_subset_1 @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93         (k1_zfmisc_1 @ 
% 0.73/0.93          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.73/0.93      inference('split', [status(esa)], ['47'])).
% 0.73/0.93  thf('139', plain,
% 0.73/0.93      (~
% 0.73/0.93       ((v5_pre_topc @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))),
% 0.73/0.93      inference('sat_resolution*', [status(thm)], ['78', '108', '137', '138'])).
% 0.73/0.93  thf('140', plain,
% 0.73/0.93      (~ (v5_pre_topc @ 
% 0.73/0.93          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)),
% 0.73/0.93      inference('simpl_trail', [status(thm)], ['48', '139'])).
% 0.73/0.93  thf('141', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_B))),
% 0.73/0.93      inference('sup-', [status(thm)], ['46', '140'])).
% 0.73/0.93  thf('142', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_E @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('143', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_F @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf(t145_tmap_1, axiom,
% 0.73/0.93    (![A:$i]:
% 0.73/0.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.73/0.93       ( ![B:$i]:
% 0.73/0.93         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.73/0.93             ( l1_pre_topc @ B ) ) =>
% 0.73/0.93           ( ![C:$i]:
% 0.73/0.93             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.73/0.93               ( ![D:$i]:
% 0.73/0.93                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.73/0.93                   ( ( r1_tsep_1 @ C @ D ) =>
% 0.73/0.93                     ( ![E:$i]:
% 0.73/0.93                       ( ( ( v1_funct_1 @ E ) & 
% 0.73/0.93                           ( v1_funct_2 @
% 0.73/0.93                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.93                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.73/0.93                           ( m1_subset_1 @
% 0.73/0.93                             E @ 
% 0.73/0.93                             ( k1_zfmisc_1 @
% 0.73/0.93                               ( k2_zfmisc_1 @
% 0.73/0.93                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.93                         ( ![F:$i]:
% 0.73/0.93                           ( ( ( v1_funct_1 @ F ) & 
% 0.73/0.93                               ( v1_funct_2 @
% 0.73/0.93                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.93                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.73/0.93                               ( m1_subset_1 @
% 0.73/0.93                                 F @ 
% 0.73/0.93                                 ( k1_zfmisc_1 @
% 0.73/0.93                                   ( k2_zfmisc_1 @
% 0.73/0.93                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.93                             ( ( r4_tsep_1 @ A @ C @ D ) =>
% 0.73/0.93                               ( ( v1_funct_1 @
% 0.73/0.93                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.73/0.93                                 ( v1_funct_2 @
% 0.73/0.93                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.93                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.73/0.93                                   ( u1_struct_0 @ B ) ) & 
% 0.73/0.93                                 ( v5_pre_topc @
% 0.73/0.93                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.93                                   ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.73/0.93                                 ( m1_subset_1 @
% 0.73/0.93                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.73/0.93                                   ( k1_zfmisc_1 @
% 0.73/0.93                                     ( k2_zfmisc_1 @
% 0.73/0.93                                       ( u1_struct_0 @
% 0.73/0.93                                         ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.73/0.93                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.73/0.93  thf('144', plain,
% 0.73/0.93      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.73/0.93         ((v2_struct_0 @ X18)
% 0.73/0.93          | ~ (v2_pre_topc @ X18)
% 0.73/0.93          | ~ (l1_pre_topc @ X18)
% 0.73/0.93          | (v2_struct_0 @ X19)
% 0.73/0.93          | ~ (m1_pre_topc @ X19 @ X20)
% 0.73/0.93          | ~ (v1_funct_1 @ X21)
% 0.73/0.93          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.73/0.93          | ~ (v5_pre_topc @ X21 @ X19 @ X18)
% 0.73/0.93          | ~ (m1_subset_1 @ X21 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))))
% 0.73/0.93          | (v5_pre_topc @ (k10_tmap_1 @ X20 @ X18 @ X22 @ X19 @ X23 @ X21) @ 
% 0.73/0.93             (k1_tsep_1 @ X20 @ X22 @ X19) @ X18)
% 0.73/0.93          | ~ (r4_tsep_1 @ X20 @ X22 @ X19)
% 0.73/0.93          | ~ (m1_subset_1 @ X23 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X18))))
% 0.73/0.93          | ~ (v5_pre_topc @ X23 @ X22 @ X18)
% 0.73/0.93          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X18))
% 0.73/0.93          | ~ (v1_funct_1 @ X23)
% 0.73/0.93          | ~ (r1_tsep_1 @ X22 @ X19)
% 0.73/0.93          | ~ (m1_pre_topc @ X22 @ X20)
% 0.73/0.93          | (v2_struct_0 @ X22)
% 0.73/0.93          | ~ (l1_pre_topc @ X20)
% 0.73/0.93          | ~ (v2_pre_topc @ X20)
% 0.73/0.93          | (v2_struct_0 @ X20))),
% 0.73/0.93      inference('cnf', [status(esa)], [t145_tmap_1])).
% 0.73/0.93  thf('145', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.93         ((v2_struct_0 @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (m1_pre_topc @ X1 @ X0)
% 0.73/0.93          | ~ (r1_tsep_1 @ X1 @ sk_D)
% 0.73/0.93          | ~ (v1_funct_1 @ X2)
% 0.73/0.93          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v5_pre_topc @ X2 @ X1 @ sk_B)
% 0.73/0.93          | ~ (m1_subset_1 @ X2 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (r4_tsep_1 @ X0 @ X1 @ sk_D)
% 0.73/0.93          | (v5_pre_topc @ (k10_tmap_1 @ X0 @ sk_B @ X1 @ sk_D @ X2 @ sk_F) @ 
% 0.73/0.93             (k1_tsep_1 @ X0 @ X1 @ sk_D) @ sk_B)
% 0.73/0.93          | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.73/0.93          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v1_funct_1 @ sk_F)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | ~ (l1_pre_topc @ sk_B)
% 0.73/0.93          | ~ (v2_pre_topc @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_B))),
% 0.73/0.93      inference('sup-', [status(thm)], ['143', '144'])).
% 0.73/0.93  thf('146', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('147', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('148', plain, ((v1_funct_1 @ sk_F)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('149', plain, ((l1_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('150', plain, ((v2_pre_topc @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('151', plain,
% 0.73/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.93         ((v2_struct_0 @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X1)
% 0.73/0.93          | ~ (m1_pre_topc @ X1 @ X0)
% 0.73/0.93          | ~ (r1_tsep_1 @ X1 @ sk_D)
% 0.73/0.93          | ~ (v1_funct_1 @ X2)
% 0.73/0.93          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v5_pre_topc @ X2 @ X1 @ sk_B)
% 0.73/0.93          | ~ (m1_subset_1 @ X2 @ 
% 0.73/0.93               (k1_zfmisc_1 @ 
% 0.73/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.73/0.93          | ~ (r4_tsep_1 @ X0 @ X1 @ sk_D)
% 0.73/0.93          | (v5_pre_topc @ (k10_tmap_1 @ X0 @ sk_B @ X1 @ sk_D @ X2 @ sk_F) @ 
% 0.73/0.93             (k1_tsep_1 @ X0 @ X1 @ sk_D) @ sk_B)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | (v2_struct_0 @ sk_B))),
% 0.73/0.93      inference('demod', [status(thm)],
% 0.73/0.93                ['145', '146', '147', '148', '149', '150'])).
% 0.73/0.93  thf('152', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         ((v2_struct_0 @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v5_pre_topc @ 
% 0.73/0.93             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.73/0.93          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.73/0.93          | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.73/0.93          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.73/0.93          | ~ (v1_funct_1 @ sk_E)
% 0.73/0.93          | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X0))),
% 0.73/0.93      inference('sup-', [status(thm)], ['142', '151'])).
% 0.73/0.93  thf('153', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('154', plain,
% 0.73/0.93      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('155', plain, ((v1_funct_1 @ sk_E)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('156', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         ((v2_struct_0 @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v5_pre_topc @ 
% 0.73/0.93             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.73/0.93          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.73/0.93          | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X0))),
% 0.73/0.93      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 0.73/0.93  thf('157', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         ((v2_struct_0 @ sk_B)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | (v2_struct_0 @ sk_A)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.73/0.93          | (v5_pre_topc @ 
% 0.73/0.93             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | (v2_struct_0 @ sk_B))),
% 0.73/0.93      inference('sup-', [status(thm)], ['141', '156'])).
% 0.73/0.93  thf('158', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         (~ (m1_pre_topc @ sk_D @ X0)
% 0.73/0.93          | (v5_pre_topc @ 
% 0.73/0.93             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.73/0.93          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.73/0.93          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.73/0.93          | ~ (l1_pre_topc @ X0)
% 0.73/0.93          | ~ (v2_pre_topc @ X0)
% 0.73/0.93          | (v2_struct_0 @ X0)
% 0.73/0.93          | (v2_struct_0 @ sk_A)
% 0.73/0.93          | (v2_struct_0 @ sk_C)
% 0.73/0.93          | (v2_struct_0 @ sk_D)
% 0.73/0.93          | (v2_struct_0 @ sk_B))),
% 0.73/0.93      inference('simplify', [status(thm)], ['157'])).
% 0.73/0.93  thf('159', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | ~ (v2_pre_topc @ sk_A)
% 0.73/0.93        | ~ (l1_pre_topc @ sk_A)
% 0.73/0.93        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.73/0.93        | (v5_pre_topc @ 
% 0.73/0.93           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.73/0.93           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.73/0.93        | ~ (m1_pre_topc @ sk_D @ sk_A))),
% 0.73/0.93      inference('sup-', [status(thm)], ['1', '158'])).
% 0.73/0.93  thf('160', plain, ((v2_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('162', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('163', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('164', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('165', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | (v5_pre_topc @ 
% 0.73/0.93           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))),
% 0.73/0.93      inference('demod', [status(thm)],
% 0.73/0.93                ['159', '160', '161', '162', '163', '164'])).
% 0.73/0.93  thf('166', plain,
% 0.73/0.93      (((v5_pre_topc @ 
% 0.73/0.93         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_A)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_B))),
% 0.73/0.93      inference('simplify', [status(thm)], ['165'])).
% 0.73/0.93  thf('167', plain,
% 0.73/0.93      (~ (v5_pre_topc @ 
% 0.73/0.93          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)),
% 0.73/0.93      inference('simpl_trail', [status(thm)], ['48', '139'])).
% 0.73/0.93  thf('168', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_B)
% 0.73/0.93        | (v2_struct_0 @ sk_D)
% 0.73/0.93        | (v2_struct_0 @ sk_C)
% 0.73/0.93        | (v2_struct_0 @ sk_A))),
% 0.73/0.93      inference('sup-', [status(thm)], ['166', '167'])).
% 0.73/0.93  thf('169', plain, (~ (v2_struct_0 @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('170', plain,
% 0.73/0.93      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.73/0.93      inference('sup-', [status(thm)], ['168', '169'])).
% 0.73/0.93  thf('171', plain, (~ (v2_struct_0 @ sk_A)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('172', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.73/0.93      inference('clc', [status(thm)], ['170', '171'])).
% 0.73/0.93  thf('173', plain, (~ (v2_struct_0 @ sk_D)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('174', plain, ((v2_struct_0 @ sk_C)),
% 0.73/0.93      inference('clc', [status(thm)], ['172', '173'])).
% 0.73/0.93  thf('175', plain, ($false), inference('demod', [status(thm)], ['0', '174'])).
% 0.73/0.93  
% 0.73/0.93  % SZS output end Refutation
% 0.73/0.93  
% 0.77/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
