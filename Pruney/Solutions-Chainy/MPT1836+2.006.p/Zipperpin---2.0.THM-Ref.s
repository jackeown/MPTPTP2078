%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VuobQDqcx8

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:14 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 351 expanded)
%              Number of leaves         :   27 ( 115 expanded)
%              Depth                    :   20
%              Number of atoms          : 2894 (30778 expanded)
%              Number of equality atoms :   13 ( 185 expanded)
%              Maximal formula depth    :   32 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t152_tmap_1,conjecture,(
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
                & ( v1_borsuk_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_borsuk_1 @ D @ A )
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
                  & ( v1_borsuk_1 @ C @ A )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_borsuk_1 @ D @ A )
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
    inference('cnf.neg',[status(esa)],[t152_tmap_1])).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v5_pre_topc @ X9 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9 ) @ X8 @ X6 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) @ ( k3_tmap_1 @ X8 @ X6 @ ( k1_tsep_1 @ X8 @ X10 @ X7 ) @ X7 @ ( k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9 ) ) @ X9 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) @ ( k3_tmap_1 @ X8 @ X6 @ ( k1_tsep_1 @ X8 @ X10 @ X7 ) @ X10 @ ( k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9 ) ) @ X11 )
      | ~ ( r4_tsep_1 @ X8 @ X10 @ X7 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v5_pre_topc @ X11 @ X10 @ X6 )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ( X8
       != ( k1_tsep_1 @ X8 @ X10 @ X7 ) )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
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
    v1_borsuk_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_borsuk_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_borsuk_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_borsuk_1 @ C @ A )
                & ( m1_pre_topc @ C @ A ) )
             => ( r4_tsep_1 @ A @ B @ C ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_borsuk_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( r4_tsep_1 @ X13 @ X12 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( v1_borsuk_1 @ X14 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t87_tsep_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A )
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
      | ~ ( v1_borsuk_1 @ X0 @ sk_A )
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
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ sk_A @ X2 )
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
      | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0 ) @ sk_A @ X2 )
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
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
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
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
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
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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

thf('48',plain,(
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

thf('49',plain,(
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
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
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
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
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
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
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
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['43'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
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

thf('78',plain,(
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
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,(
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
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
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
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['74','87'])).

thf('89',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
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

thf('108',plain,(
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
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
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
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,(
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
    inference('sup-',[status(thm)],['105','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
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
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['104','117'])).

thf('119',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['118','119','120','121','122'])).

thf('124',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['43'])).

thf('135',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['73','103','133','134'])).

thf('136',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['44','135'])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['0','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VuobQDqcx8
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:30:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.51/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.72  % Solved by: fo/fo7.sh
% 0.51/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.72  % done 242 iterations in 0.235s
% 0.51/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.72  % SZS output start Refutation
% 0.51/0.72  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.51/0.72  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.51/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.51/0.72  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.51/0.72  thf(sk_F_type, type, sk_F: $i).
% 0.51/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.72  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.51/0.72  thf(sk_E_type, type, sk_E: $i).
% 0.51/0.72  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.51/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.72  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.51/0.72  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.51/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.72  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.51/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.72  thf(t152_tmap_1, conjecture,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.51/0.72             ( l1_pre_topc @ B ) ) =>
% 0.51/0.72           ( ![C:$i]:
% 0.51/0.72             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_borsuk_1 @ C @ A ) & 
% 0.51/0.72                 ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.72               ( ![D:$i]:
% 0.51/0.72                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_borsuk_1 @ D @ A ) & 
% 0.51/0.72                     ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.72                   ( ![E:$i]:
% 0.51/0.72                     ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.72                         ( v1_funct_2 @
% 0.51/0.72                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72                         ( v5_pre_topc @ E @ C @ B ) & 
% 0.51/0.72                         ( m1_subset_1 @
% 0.51/0.72                           E @ 
% 0.51/0.72                           ( k1_zfmisc_1 @
% 0.51/0.72                             ( k2_zfmisc_1 @
% 0.51/0.72                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.72                       ( ![F:$i]:
% 0.51/0.72                         ( ( ( v1_funct_1 @ F ) & 
% 0.51/0.72                             ( v1_funct_2 @
% 0.51/0.72                               F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72                             ( v5_pre_topc @ F @ D @ B ) & 
% 0.51/0.72                             ( m1_subset_1 @
% 0.51/0.72                               F @ 
% 0.51/0.72                               ( k1_zfmisc_1 @
% 0.51/0.72                                 ( k2_zfmisc_1 @
% 0.51/0.72                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.72                           ( ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) & 
% 0.51/0.72                               ( r2_funct_2 @
% 0.51/0.72                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.51/0.72                                 ( k3_tmap_1 @
% 0.51/0.72                                   A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.51/0.72                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.51/0.72                                 E ) & 
% 0.51/0.72                               ( r2_funct_2 @
% 0.51/0.72                                 ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.51/0.72                                 ( k3_tmap_1 @
% 0.51/0.72                                   A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.51/0.72                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.51/0.72                                 F ) ) =>
% 0.51/0.72                             ( ( v1_funct_1 @
% 0.51/0.72                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.51/0.72                               ( v1_funct_2 @
% 0.51/0.72                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72                               ( v5_pre_topc @
% 0.51/0.72                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ A @ B ) & 
% 0.51/0.72                               ( m1_subset_1 @
% 0.51/0.72                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72                                 ( k1_zfmisc_1 @
% 0.51/0.72                                   ( k2_zfmisc_1 @
% 0.51/0.72                                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.72    (~( ![A:$i]:
% 0.51/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.72            ( l1_pre_topc @ A ) ) =>
% 0.51/0.72          ( ![B:$i]:
% 0.51/0.72            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.51/0.72                ( l1_pre_topc @ B ) ) =>
% 0.51/0.72              ( ![C:$i]:
% 0.51/0.72                ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_borsuk_1 @ C @ A ) & 
% 0.51/0.72                    ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.72                  ( ![D:$i]:
% 0.51/0.72                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_borsuk_1 @ D @ A ) & 
% 0.51/0.72                        ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.72                      ( ![E:$i]:
% 0.51/0.72                        ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.72                            ( v1_funct_2 @
% 0.51/0.72                              E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72                            ( v5_pre_topc @ E @ C @ B ) & 
% 0.51/0.72                            ( m1_subset_1 @
% 0.51/0.72                              E @ 
% 0.51/0.72                              ( k1_zfmisc_1 @
% 0.51/0.72                                ( k2_zfmisc_1 @
% 0.51/0.72                                  ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.72                          ( ![F:$i]:
% 0.51/0.72                            ( ( ( v1_funct_1 @ F ) & 
% 0.51/0.72                                ( v1_funct_2 @
% 0.51/0.72                                  F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72                                ( v5_pre_topc @ F @ D @ B ) & 
% 0.51/0.72                                ( m1_subset_1 @
% 0.51/0.72                                  F @ 
% 0.51/0.72                                  ( k1_zfmisc_1 @
% 0.51/0.72                                    ( k2_zfmisc_1 @
% 0.51/0.72                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.72                              ( ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) & 
% 0.51/0.72                                  ( r2_funct_2 @
% 0.51/0.72                                    ( u1_struct_0 @ C ) @ 
% 0.51/0.72                                    ( u1_struct_0 @ B ) @ 
% 0.51/0.72                                    ( k3_tmap_1 @
% 0.51/0.72                                      A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.51/0.72                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.51/0.72                                    E ) & 
% 0.51/0.72                                  ( r2_funct_2 @
% 0.51/0.72                                    ( u1_struct_0 @ D ) @ 
% 0.51/0.72                                    ( u1_struct_0 @ B ) @ 
% 0.51/0.72                                    ( k3_tmap_1 @
% 0.51/0.72                                      A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.51/0.72                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.51/0.72                                    F ) ) =>
% 0.51/0.72                                ( ( v1_funct_1 @
% 0.51/0.72                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.51/0.72                                  ( v1_funct_2 @
% 0.51/0.72                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72                                    ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72                                  ( v5_pre_topc @
% 0.51/0.72                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72                                    A @ B ) & 
% 0.51/0.72                                  ( m1_subset_1 @
% 0.51/0.72                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72                                    ( k1_zfmisc_1 @
% 0.51/0.72                                      ( k2_zfmisc_1 @
% 0.51/0.72                                        ( u1_struct_0 @ A ) @ 
% 0.51/0.72                                        ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.51/0.72    inference('cnf.neg', [status(esa)], [t152_tmap_1])).
% 0.51/0.72  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('1', plain,
% 0.51/0.72      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.72        (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.51/0.72         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.51/0.72        sk_E)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('2', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('3', plain,
% 0.51/0.72      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.72        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ 
% 0.51/0.72         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.51/0.72        sk_E)),
% 0.51/0.72      inference('demod', [status(thm)], ['1', '2'])).
% 0.51/0.72  thf('4', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t151_tmap_1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.51/0.72             ( l1_pre_topc @ B ) ) =>
% 0.51/0.72           ( ![C:$i]:
% 0.51/0.72             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.72               ( ![D:$i]:
% 0.51/0.72                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.51/0.72                   ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) =>
% 0.51/0.72                     ( ![E:$i]:
% 0.51/0.72                       ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.72                           ( v1_funct_2 @
% 0.51/0.72                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.51/0.72                           ( m1_subset_1 @
% 0.51/0.72                             E @ 
% 0.51/0.72                             ( k1_zfmisc_1 @
% 0.51/0.72                               ( k2_zfmisc_1 @
% 0.51/0.72                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.72                         ( ![F:$i]:
% 0.51/0.72                           ( ( ( v1_funct_1 @ F ) & 
% 0.51/0.72                               ( v1_funct_2 @
% 0.51/0.72                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.51/0.72                               ( m1_subset_1 @
% 0.51/0.72                                 F @ 
% 0.51/0.72                                 ( k1_zfmisc_1 @
% 0.51/0.72                                   ( k2_zfmisc_1 @
% 0.51/0.72                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.72                             ( ( ( r2_funct_2 @
% 0.51/0.72                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.51/0.72                                   ( k3_tmap_1 @
% 0.51/0.72                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.51/0.72                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.51/0.72                                   E ) & 
% 0.51/0.72                                 ( r2_funct_2 @
% 0.51/0.72                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.51/0.72                                   ( k3_tmap_1 @
% 0.51/0.72                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.51/0.72                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.51/0.72                                   F ) & 
% 0.51/0.72                                 ( r4_tsep_1 @ A @ C @ D ) ) =>
% 0.51/0.72                               ( ( v1_funct_1 @
% 0.51/0.72                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.51/0.72                                 ( v1_funct_2 @
% 0.51/0.72                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72                                 ( v5_pre_topc @
% 0.51/0.72                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72                                   A @ B ) & 
% 0.51/0.72                                 ( m1_subset_1 @
% 0.51/0.72                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72                                   ( k1_zfmisc_1 @
% 0.51/0.72                                     ( k2_zfmisc_1 @
% 0.51/0.72                                       ( u1_struct_0 @ A ) @ 
% 0.51/0.72                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.72  thf('5', plain,
% 0.51/0.72      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.72         ((v2_struct_0 @ X6)
% 0.51/0.72          | ~ (v2_pre_topc @ X6)
% 0.51/0.72          | ~ (l1_pre_topc @ X6)
% 0.51/0.72          | (v2_struct_0 @ X7)
% 0.51/0.72          | ~ (m1_pre_topc @ X7 @ X8)
% 0.51/0.72          | ~ (v1_funct_1 @ X9)
% 0.51/0.72          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 0.51/0.72          | ~ (v5_pre_topc @ X9 @ X7 @ X6)
% 0.51/0.72          | ~ (m1_subset_1 @ X9 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 0.51/0.72          | (v5_pre_topc @ (k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9) @ X8 @ 
% 0.51/0.72             X6)
% 0.51/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6) @ 
% 0.51/0.72               (k3_tmap_1 @ X8 @ X6 @ (k1_tsep_1 @ X8 @ X10 @ X7) @ X7 @ 
% 0.51/0.72                (k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9)) @ 
% 0.51/0.72               X9)
% 0.51/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6) @ 
% 0.51/0.72               (k3_tmap_1 @ X8 @ X6 @ (k1_tsep_1 @ X8 @ X10 @ X7) @ X10 @ 
% 0.51/0.72                (k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9)) @ 
% 0.51/0.72               X11)
% 0.51/0.72          | ~ (r4_tsep_1 @ X8 @ X10 @ X7)
% 0.51/0.72          | ~ (m1_subset_1 @ X11 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))))
% 0.51/0.72          | ~ (v5_pre_topc @ X11 @ X10 @ X6)
% 0.51/0.72          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))
% 0.51/0.72          | ~ (v1_funct_1 @ X11)
% 0.51/0.72          | ((X8) != (k1_tsep_1 @ X8 @ X10 @ X7))
% 0.51/0.72          | ~ (m1_pre_topc @ X10 @ X8)
% 0.51/0.72          | (v2_struct_0 @ X10)
% 0.51/0.72          | ~ (l1_pre_topc @ X8)
% 0.51/0.72          | ~ (v2_pre_topc @ X8)
% 0.51/0.72          | (v2_struct_0 @ X8))),
% 0.51/0.72      inference('cnf', [status(esa)], [t151_tmap_1])).
% 0.51/0.72  thf('6', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.51/0.72             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.51/0.72              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.51/0.72             X0)
% 0.51/0.72          | (v2_struct_0 @ sk_A)
% 0.51/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.72          | (v2_struct_0 @ sk_C)
% 0.51/0.72          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.51/0.72          | ((sk_A) != (k1_tsep_1 @ sk_A @ sk_C @ sk_D))
% 0.51/0.72          | ~ (v1_funct_1 @ X1)
% 0.51/0.72          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.51/0.72          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.51/0.72          | ~ (m1_subset_1 @ X1 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.51/0.72          | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.51/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.51/0.72               (k3_tmap_1 @ sk_A @ X2 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.51/0.72                sk_C @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.51/0.72               X1)
% 0.51/0.72          | (v5_pre_topc @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.51/0.72             sk_A @ X2)
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.51/0.72          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.51/0.72          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.51/0.72          | ~ (v1_funct_1 @ X0)
% 0.51/0.72          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.51/0.72          | (v2_struct_0 @ sk_D)
% 0.51/0.72          | ~ (l1_pre_topc @ X2)
% 0.51/0.72          | ~ (v2_pre_topc @ X2)
% 0.51/0.72          | (v2_struct_0 @ X2))),
% 0.51/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.72  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('9', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('10', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('11', plain, ((v1_borsuk_1 @ sk_D @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('12', plain, ((v1_borsuk_1 @ sk_C @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t87_tsep_1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.51/0.72           ( ![C:$i]:
% 0.51/0.72             ( ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.51/0.72               ( r4_tsep_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.51/0.72  thf('13', plain,
% 0.51/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.72         (~ (v1_borsuk_1 @ X12 @ X13)
% 0.51/0.72          | ~ (m1_pre_topc @ X12 @ X13)
% 0.51/0.72          | (r4_tsep_1 @ X13 @ X12 @ X14)
% 0.51/0.72          | ~ (m1_pre_topc @ X14 @ X13)
% 0.51/0.72          | ~ (v1_borsuk_1 @ X14 @ X13)
% 0.51/0.72          | ~ (l1_pre_topc @ X13)
% 0.51/0.72          | ~ (v2_pre_topc @ X13)
% 0.51/0.72          | (v2_struct_0 @ X13))),
% 0.51/0.72      inference('cnf', [status(esa)], [t87_tsep_1])).
% 0.51/0.72  thf('14', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((v2_struct_0 @ sk_A)
% 0.51/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.72          | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 0.51/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.51/0.72          | (r4_tsep_1 @ sk_A @ sk_C @ X0)
% 0.51/0.72          | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.72  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('18', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((v2_struct_0 @ sk_A)
% 0.51/0.72          | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 0.51/0.72          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.51/0.72          | (r4_tsep_1 @ sk_A @ sk_C @ X0))),
% 0.51/0.72      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.51/0.72  thf('19', plain,
% 0.51/0.72      (((r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.51/0.72        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.51/0.72        | (v2_struct_0 @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['11', '18'])).
% 0.51/0.72  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('21', plain, (((r4_tsep_1 @ sk_A @ sk_C @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.51/0.72      inference('demod', [status(thm)], ['19', '20'])).
% 0.51/0.72  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('23', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.51/0.72      inference('clc', [status(thm)], ['21', '22'])).
% 0.51/0.72  thf('24', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('26', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         (~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.51/0.72             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.51/0.72              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.51/0.72             X0)
% 0.51/0.72          | (v2_struct_0 @ sk_A)
% 0.51/0.72          | (v2_struct_0 @ sk_C)
% 0.51/0.72          | ((sk_A) != (sk_A))
% 0.51/0.72          | ~ (v1_funct_1 @ X1)
% 0.51/0.72          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.51/0.72          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.51/0.72          | ~ (m1_subset_1 @ X1 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.51/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.51/0.72               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.51/0.72                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.51/0.72               X1)
% 0.51/0.72          | (v5_pre_topc @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.51/0.72             sk_A @ X2)
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.51/0.72          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.51/0.72          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.51/0.72          | ~ (v1_funct_1 @ X0)
% 0.51/0.72          | (v2_struct_0 @ sk_D)
% 0.51/0.72          | ~ (l1_pre_topc @ X2)
% 0.51/0.72          | ~ (v2_pre_topc @ X2)
% 0.51/0.72          | (v2_struct_0 @ X2))),
% 0.51/0.72      inference('demod', [status(thm)],
% 0.51/0.72                ['6', '7', '8', '9', '10', '23', '24', '25'])).
% 0.51/0.72  thf('27', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         ((v2_struct_0 @ X2)
% 0.51/0.72          | ~ (v2_pre_topc @ X2)
% 0.51/0.72          | ~ (l1_pre_topc @ X2)
% 0.51/0.72          | (v2_struct_0 @ sk_D)
% 0.51/0.72          | ~ (v1_funct_1 @ X0)
% 0.51/0.72          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.51/0.72          | ~ (v5_pre_topc @ X0 @ sk_D @ X2)
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.51/0.72          | (v5_pre_topc @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0) @ 
% 0.51/0.72             sk_A @ X2)
% 0.51/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.51/0.72               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.51/0.72                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.51/0.72               X1)
% 0.51/0.72          | ~ (m1_subset_1 @ X1 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.51/0.72          | ~ (v5_pre_topc @ X1 @ sk_C @ X2)
% 0.51/0.72          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.51/0.72          | ~ (v1_funct_1 @ X1)
% 0.51/0.72          | (v2_struct_0 @ sk_C)
% 0.51/0.72          | (v2_struct_0 @ sk_A)
% 0.51/0.72          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.51/0.72               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.51/0.72                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X1 @ X0)) @ 
% 0.51/0.72               X0))),
% 0.51/0.72      inference('simplify', [status(thm)], ['26'])).
% 0.51/0.72  thf('28', plain,
% 0.51/0.72      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.72           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.51/0.72            (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.51/0.72           sk_F)
% 0.51/0.72        | (v2_struct_0 @ sk_A)
% 0.51/0.72        | (v2_struct_0 @ sk_C)
% 0.51/0.72        | ~ (v1_funct_1 @ sk_E)
% 0.51/0.72        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.51/0.72        | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.51/0.72        | ~ (m1_subset_1 @ sk_E @ 
% 0.51/0.72             (k1_zfmisc_1 @ 
% 0.51/0.72              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.51/0.72        | (v5_pre_topc @ 
% 0.51/0.72           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.51/0.72        | ~ (m1_subset_1 @ sk_F @ 
% 0.51/0.72             (k1_zfmisc_1 @ 
% 0.51/0.72              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.51/0.72        | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.51/0.72        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.51/0.72        | ~ (v1_funct_1 @ sk_F)
% 0.51/0.72        | (v2_struct_0 @ sk_D)
% 0.51/0.72        | ~ (l1_pre_topc @ sk_B)
% 0.51/0.72        | ~ (v2_pre_topc @ sk_B)
% 0.51/0.72        | (v2_struct_0 @ sk_B))),
% 0.51/0.72      inference('sup-', [status(thm)], ['3', '27'])).
% 0.51/0.72  thf('29', plain,
% 0.51/0.72      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.72        (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.51/0.72         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.51/0.72        sk_F)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('30', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('31', plain,
% 0.51/0.72      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.51/0.72        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.51/0.72         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.51/0.72        sk_F)),
% 0.51/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.51/0.72  thf('32', plain, ((v1_funct_1 @ sk_E)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('33', plain,
% 0.51/0.72      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('34', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('35', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_E @ 
% 0.51/0.72        (k1_zfmisc_1 @ 
% 0.51/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('36', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_F @ 
% 0.51/0.72        (k1_zfmisc_1 @ 
% 0.51/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('37', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('38', plain,
% 0.51/0.72      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('39', plain, ((v1_funct_1 @ sk_F)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('42', plain,
% 0.51/0.72      (((v2_struct_0 @ sk_A)
% 0.51/0.72        | (v2_struct_0 @ sk_C)
% 0.51/0.72        | (v5_pre_topc @ 
% 0.51/0.72           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.51/0.72        | (v2_struct_0 @ sk_D)
% 0.51/0.72        | (v2_struct_0 @ sk_B))),
% 0.51/0.72      inference('demod', [status(thm)],
% 0.51/0.72                ['28', '31', '32', '33', '34', '35', '36', '37', '38', '39', 
% 0.51/0.72                 '40', '41'])).
% 0.51/0.72  thf('43', plain,
% 0.51/0.72      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.51/0.72        | ~ (v1_funct_2 @ 
% 0.51/0.72             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.72             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.51/0.72        | ~ (v5_pre_topc @ 
% 0.51/0.72             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.51/0.72             sk_B)
% 0.51/0.72        | ~ (m1_subset_1 @ 
% 0.51/0.72             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.72             (k1_zfmisc_1 @ 
% 0.51/0.72              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('44', plain,
% 0.51/0.72      ((~ (v5_pre_topc @ 
% 0.51/0.72           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))
% 0.51/0.72         <= (~
% 0.51/0.72             ((v5_pre_topc @ 
% 0.51/0.72               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.51/0.72               sk_B)))),
% 0.51/0.72      inference('split', [status(esa)], ['43'])).
% 0.51/0.72  thf('45', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('46', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_F @ 
% 0.51/0.72        (k1_zfmisc_1 @ 
% 0.51/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('47', plain,
% 0.51/0.72      ((m1_subset_1 @ sk_E @ 
% 0.51/0.72        (k1_zfmisc_1 @ 
% 0.51/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(dt_k10_tmap_1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.51/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.72         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.51/0.72         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 0.51/0.72         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.51/0.72         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 0.51/0.72         ( v1_funct_1 @ E ) & 
% 0.51/0.72         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72         ( m1_subset_1 @
% 0.51/0.72           E @ 
% 0.51/0.72           ( k1_zfmisc_1 @
% 0.51/0.72             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.51/0.72         ( v1_funct_1 @ F ) & 
% 0.51/0.72         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72         ( m1_subset_1 @
% 0.51/0.72           F @ 
% 0.51/0.72           ( k1_zfmisc_1 @
% 0.51/0.72             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.51/0.72       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.51/0.72         ( v1_funct_2 @
% 0.51/0.72           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 0.51/0.72         ( m1_subset_1 @
% 0.51/0.72           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.51/0.72           ( k1_zfmisc_1 @
% 0.51/0.72             ( k2_zfmisc_1 @
% 0.51/0.72               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.51/0.72               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.51/0.72  thf('48', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.72         (~ (m1_subset_1 @ X0 @ 
% 0.51/0.72             (k1_zfmisc_1 @ 
% 0.51/0.72              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.51/0.72          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.51/0.72          | ~ (v1_funct_1 @ X0)
% 0.51/0.72          | ~ (m1_pre_topc @ X3 @ X4)
% 0.51/0.72          | (v2_struct_0 @ X3)
% 0.51/0.72          | ~ (m1_pre_topc @ X1 @ X4)
% 0.51/0.72          | (v2_struct_0 @ X1)
% 0.51/0.72          | ~ (l1_pre_topc @ X2)
% 0.51/0.72          | ~ (v2_pre_topc @ X2)
% 0.51/0.72          | (v2_struct_0 @ X2)
% 0.51/0.72          | ~ (l1_pre_topc @ X4)
% 0.51/0.72          | ~ (v2_pre_topc @ X4)
% 0.51/0.72          | (v2_struct_0 @ X4)
% 0.51/0.72          | ~ (v1_funct_1 @ X5)
% 0.51/0.72          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.51/0.72          | ~ (m1_subset_1 @ X5 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.51/0.72          | (v1_funct_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5)))),
% 0.51/0.72      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.51/0.72  thf('49', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.51/0.72          | ~ (m1_subset_1 @ X0 @ 
% 0.51/0.72               (k1_zfmisc_1 @ 
% 0.51/0.72                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.51/0.72          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.51/0.72          | ~ (v1_funct_1 @ X0)
% 0.51/0.72          | (v2_struct_0 @ X2)
% 0.51/0.72          | ~ (v2_pre_topc @ X2)
% 0.51/0.72          | ~ (l1_pre_topc @ X2)
% 0.51/0.72          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | ~ (v2_pre_topc @ sk_B)
% 0.51/0.73          | ~ (l1_pre_topc @ sk_B)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.51/0.73          | (v2_struct_0 @ X1)
% 0.51/0.73          | ~ (m1_pre_topc @ X1 @ X2)
% 0.51/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.51/0.73          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.51/0.73  thf('50', plain, ((v2_pre_topc @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('52', plain, ((v1_funct_1 @ sk_E)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('53', plain,
% 0.51/0.73      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('54', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.51/0.73          | ~ (m1_subset_1 @ X0 @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.51/0.73          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | ~ (v1_funct_1 @ X0)
% 0.51/0.73          | (v2_struct_0 @ X2)
% 0.51/0.73          | ~ (v2_pre_topc @ X2)
% 0.51/0.73          | ~ (l1_pre_topc @ X2)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.51/0.73          | (v2_struct_0 @ X1)
% 0.51/0.73          | ~ (m1_pre_topc @ X1 @ X2))),
% 0.51/0.73      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.51/0.73  thf('55', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_D)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | ~ (l1_pre_topc @ X0)
% 0.51/0.73          | ~ (v2_pre_topc @ X0)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.51/0.73          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['46', '54'])).
% 0.51/0.73  thf('56', plain, ((v1_funct_1 @ sk_F)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('57', plain,
% 0.51/0.73      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('58', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_D)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | ~ (l1_pre_topc @ X0)
% 0.51/0.73          | ~ (v2_pre_topc @ X0)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.51/0.73      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.51/0.73  thf('59', plain,
% 0.51/0.73      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.51/0.73        | (v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v2_struct_0 @ sk_B)
% 0.51/0.73        | (v2_struct_0 @ sk_C)
% 0.51/0.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.51/0.73        | (v2_struct_0 @ sk_D))),
% 0.51/0.73      inference('sup-', [status(thm)], ['45', '58'])).
% 0.51/0.73  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('62', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('63', plain,
% 0.51/0.73      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.51/0.73        | (v2_struct_0 @ sk_A)
% 0.51/0.73        | (v2_struct_0 @ sk_B)
% 0.51/0.73        | (v2_struct_0 @ sk_C)
% 0.51/0.73        | (v2_struct_0 @ sk_D))),
% 0.51/0.73      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.51/0.73  thf('64', plain,
% 0.51/0.73      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.51/0.73      inference('split', [status(esa)], ['43'])).
% 0.51/0.73  thf('65', plain,
% 0.51/0.73      ((((v2_struct_0 @ sk_D)
% 0.51/0.73         | (v2_struct_0 @ sk_C)
% 0.51/0.73         | (v2_struct_0 @ sk_B)
% 0.51/0.73         | (v2_struct_0 @ sk_A)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.51/0.73  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('67', plain,
% 0.51/0.73      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['65', '66'])).
% 0.51/0.73  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('69', plain,
% 0.51/0.73      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.51/0.73      inference('clc', [status(thm)], ['67', '68'])).
% 0.51/0.73  thf('70', plain, (~ (v2_struct_0 @ sk_D)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('71', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_C))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.51/0.73      inference('clc', [status(thm)], ['69', '70'])).
% 0.51/0.73  thf('72', plain, (~ (v2_struct_0 @ sk_C)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('73', plain,
% 0.51/0.73      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['71', '72'])).
% 0.51/0.73  thf('74', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('75', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_F @ 
% 0.51/0.73        (k1_zfmisc_1 @ 
% 0.51/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('76', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_E @ 
% 0.51/0.73        (k1_zfmisc_1 @ 
% 0.51/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('77', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X0 @ 
% 0.51/0.73             (k1_zfmisc_1 @ 
% 0.51/0.73              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.51/0.73          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.51/0.73          | ~ (v1_funct_1 @ X0)
% 0.51/0.73          | ~ (m1_pre_topc @ X3 @ X4)
% 0.51/0.73          | (v2_struct_0 @ X3)
% 0.51/0.73          | ~ (m1_pre_topc @ X1 @ X4)
% 0.51/0.73          | (v2_struct_0 @ X1)
% 0.51/0.73          | ~ (l1_pre_topc @ X2)
% 0.51/0.73          | ~ (v2_pre_topc @ X2)
% 0.51/0.73          | (v2_struct_0 @ X2)
% 0.51/0.73          | ~ (l1_pre_topc @ X4)
% 0.51/0.73          | ~ (v2_pre_topc @ X4)
% 0.51/0.73          | (v2_struct_0 @ X4)
% 0.51/0.73          | ~ (v1_funct_1 @ X5)
% 0.51/0.73          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.51/0.73          | ~ (m1_subset_1 @ X5 @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.51/0.73          | (v1_funct_2 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.51/0.73             (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ (u1_struct_0 @ X2)))),
% 0.51/0.73      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.51/0.73  thf('78', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.51/0.73           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | ~ (m1_subset_1 @ X2 @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.51/0.73          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | ~ (v1_funct_1 @ X2)
% 0.51/0.73          | (v2_struct_0 @ X1)
% 0.51/0.73          | ~ (v2_pre_topc @ X1)
% 0.51/0.73          | ~ (l1_pre_topc @ X1)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | ~ (v2_pre_topc @ sk_B)
% 0.51/0.73          | ~ (l1_pre_topc @ sk_B)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | ~ (m1_pre_topc @ X0 @ X1)
% 0.51/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.51/0.73          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['76', '77'])).
% 0.51/0.73  thf('79', plain, ((v2_pre_topc @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('80', plain, ((l1_pre_topc @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('81', plain, ((v1_funct_1 @ sk_E)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('82', plain,
% 0.51/0.73      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('83', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.51/0.73           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | ~ (m1_subset_1 @ X2 @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.51/0.73          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | ~ (v1_funct_1 @ X2)
% 0.51/0.73          | (v2_struct_0 @ X1)
% 0.51/0.73          | ~ (v2_pre_topc @ X1)
% 0.51/0.73          | ~ (l1_pre_topc @ X1)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.51/0.73      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.51/0.73  thf('84', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_D)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | ~ (l1_pre_topc @ X0)
% 0.51/0.73          | ~ (v2_pre_topc @ X0)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.51/0.73          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | (v1_funct_2 @ 
% 0.51/0.73             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.51/0.73             (u1_struct_0 @ sk_B)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['75', '83'])).
% 0.51/0.73  thf('85', plain, ((v1_funct_1 @ sk_F)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('86', plain,
% 0.51/0.73      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('87', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_D)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | ~ (l1_pre_topc @ X0)
% 0.51/0.73          | ~ (v2_pre_topc @ X0)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | (v1_funct_2 @ 
% 0.51/0.73             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.51/0.73             (u1_struct_0 @ sk_B)))),
% 0.51/0.73      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.51/0.73  thf('88', plain,
% 0.51/0.73      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.51/0.73         (u1_struct_0 @ sk_B))
% 0.51/0.73        | (v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v2_struct_0 @ sk_B)
% 0.51/0.73        | (v2_struct_0 @ sk_C)
% 0.51/0.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.51/0.73        | (v2_struct_0 @ sk_D))),
% 0.51/0.73      inference('sup-', [status(thm)], ['74', '87'])).
% 0.51/0.73  thf('89', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('92', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('93', plain,
% 0.51/0.73      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.51/0.73        | (v2_struct_0 @ sk_A)
% 0.51/0.73        | (v2_struct_0 @ sk_B)
% 0.51/0.73        | (v2_struct_0 @ sk_C)
% 0.51/0.73        | (v2_struct_0 @ sk_D))),
% 0.51/0.73      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.51/0.73  thf('94', plain,
% 0.51/0.73      ((~ (v1_funct_2 @ 
% 0.51/0.73           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_2 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.73      inference('split', [status(esa)], ['43'])).
% 0.51/0.73  thf('95', plain,
% 0.51/0.73      ((((v2_struct_0 @ sk_D)
% 0.51/0.73         | (v2_struct_0 @ sk_C)
% 0.51/0.73         | (v2_struct_0 @ sk_B)
% 0.51/0.73         | (v2_struct_0 @ sk_A)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_2 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['93', '94'])).
% 0.51/0.73  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('97', plain,
% 0.51/0.73      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_2 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['95', '96'])).
% 0.51/0.73  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('99', plain,
% 0.51/0.73      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_2 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.73      inference('clc', [status(thm)], ['97', '98'])).
% 0.51/0.73  thf('100', plain, (~ (v2_struct_0 @ sk_D)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('101', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_C))
% 0.51/0.73         <= (~
% 0.51/0.73             ((v1_funct_2 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.73      inference('clc', [status(thm)], ['99', '100'])).
% 0.51/0.73  thf('102', plain, (~ (v2_struct_0 @ sk_C)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('103', plain,
% 0.51/0.73      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['101', '102'])).
% 0.51/0.73  thf('104', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('105', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_F @ 
% 0.51/0.73        (k1_zfmisc_1 @ 
% 0.51/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('106', plain,
% 0.51/0.73      ((m1_subset_1 @ sk_E @ 
% 0.51/0.73        (k1_zfmisc_1 @ 
% 0.51/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('107', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.73         (~ (m1_subset_1 @ X0 @ 
% 0.51/0.73             (k1_zfmisc_1 @ 
% 0.51/0.73              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.51/0.73          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.51/0.73          | ~ (v1_funct_1 @ X0)
% 0.51/0.73          | ~ (m1_pre_topc @ X3 @ X4)
% 0.51/0.73          | (v2_struct_0 @ X3)
% 0.51/0.73          | ~ (m1_pre_topc @ X1 @ X4)
% 0.51/0.73          | (v2_struct_0 @ X1)
% 0.51/0.73          | ~ (l1_pre_topc @ X2)
% 0.51/0.73          | ~ (v2_pre_topc @ X2)
% 0.51/0.73          | (v2_struct_0 @ X2)
% 0.51/0.73          | ~ (l1_pre_topc @ X4)
% 0.51/0.73          | ~ (v2_pre_topc @ X4)
% 0.51/0.73          | (v2_struct_0 @ X4)
% 0.51/0.73          | ~ (v1_funct_1 @ X5)
% 0.51/0.73          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.51/0.73          | ~ (m1_subset_1 @ X5 @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.51/0.73          | (m1_subset_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.51/0.73             (k1_zfmisc_1 @ 
% 0.51/0.73              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ 
% 0.51/0.73               (u1_struct_0 @ X2)))))),
% 0.51/0.73      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.51/0.73  thf('108', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.51/0.73           (k1_zfmisc_1 @ 
% 0.51/0.73            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.51/0.73             (u1_struct_0 @ sk_B))))
% 0.51/0.73          | ~ (m1_subset_1 @ X2 @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.51/0.73          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | ~ (v1_funct_1 @ X2)
% 0.51/0.73          | (v2_struct_0 @ X1)
% 0.51/0.73          | ~ (v2_pre_topc @ X1)
% 0.51/0.73          | ~ (l1_pre_topc @ X1)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | ~ (v2_pre_topc @ sk_B)
% 0.51/0.73          | ~ (l1_pre_topc @ sk_B)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | ~ (m1_pre_topc @ X0 @ X1)
% 0.51/0.73          | ~ (v1_funct_1 @ sk_E)
% 0.51/0.73          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['106', '107'])).
% 0.51/0.73  thf('109', plain, ((v2_pre_topc @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('110', plain, ((l1_pre_topc @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('111', plain, ((v1_funct_1 @ sk_E)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('112', plain,
% 0.51/0.73      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('113', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.51/0.73           (k1_zfmisc_1 @ 
% 0.51/0.73            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.51/0.73             (u1_struct_0 @ sk_B))))
% 0.51/0.73          | ~ (m1_subset_1 @ X2 @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.51/0.73          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | ~ (v1_funct_1 @ X2)
% 0.51/0.73          | (v2_struct_0 @ X1)
% 0.51/0.73          | ~ (v2_pre_topc @ X1)
% 0.51/0.73          | ~ (l1_pre_topc @ X1)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.51/0.73      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.51/0.73  thf('114', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_D)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | ~ (l1_pre_topc @ X0)
% 0.51/0.73          | ~ (v2_pre_topc @ X0)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | ~ (v1_funct_1 @ sk_F)
% 0.51/0.73          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.51/0.73          | (m1_subset_1 @ 
% 0.51/0.73             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73             (k1_zfmisc_1 @ 
% 0.51/0.73              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.51/0.73               (u1_struct_0 @ sk_B)))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['105', '113'])).
% 0.51/0.73  thf('115', plain, ((v1_funct_1 @ sk_F)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('116', plain,
% 0.51/0.73      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('117', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (~ (m1_pre_topc @ sk_D @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_D)
% 0.51/0.73          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.51/0.73          | (v2_struct_0 @ sk_C)
% 0.51/0.73          | (v2_struct_0 @ sk_B)
% 0.51/0.73          | ~ (l1_pre_topc @ X0)
% 0.51/0.73          | ~ (v2_pre_topc @ X0)
% 0.51/0.73          | (v2_struct_0 @ X0)
% 0.51/0.73          | (m1_subset_1 @ 
% 0.51/0.73             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73             (k1_zfmisc_1 @ 
% 0.51/0.73              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.51/0.73               (u1_struct_0 @ sk_B)))))),
% 0.51/0.73      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.51/0.73  thf('118', plain,
% 0.51/0.73      (((m1_subset_1 @ 
% 0.51/0.73         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73         (k1_zfmisc_1 @ 
% 0.51/0.73          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.51/0.73           (u1_struct_0 @ sk_B))))
% 0.51/0.73        | (v2_struct_0 @ sk_A)
% 0.51/0.73        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.73        | (v2_struct_0 @ sk_B)
% 0.51/0.73        | (v2_struct_0 @ sk_C)
% 0.51/0.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.51/0.73        | (v2_struct_0 @ sk_D))),
% 0.51/0.73      inference('sup-', [status(thm)], ['104', '117'])).
% 0.51/0.73  thf('119', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('120', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('122', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('123', plain,
% 0.51/0.73      (((m1_subset_1 @ 
% 0.51/0.73         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73         (k1_zfmisc_1 @ 
% 0.51/0.73          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.51/0.73        | (v2_struct_0 @ sk_A)
% 0.51/0.73        | (v2_struct_0 @ sk_B)
% 0.51/0.73        | (v2_struct_0 @ sk_C)
% 0.51/0.73        | (v2_struct_0 @ sk_D))),
% 0.51/0.73      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 0.51/0.73  thf('124', plain,
% 0.51/0.73      ((~ (m1_subset_1 @ 
% 0.51/0.73           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73           (k1_zfmisc_1 @ 
% 0.51/0.73            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.51/0.73         <= (~
% 0.51/0.73             ((m1_subset_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.51/0.73      inference('split', [status(esa)], ['43'])).
% 0.51/0.73  thf('125', plain,
% 0.51/0.73      ((((v2_struct_0 @ sk_D)
% 0.51/0.73         | (v2_struct_0 @ sk_C)
% 0.51/0.73         | (v2_struct_0 @ sk_B)
% 0.51/0.73         | (v2_struct_0 @ sk_A)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((m1_subset_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['123', '124'])).
% 0.51/0.73  thf('126', plain, (~ (v2_struct_0 @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('127', plain,
% 0.51/0.73      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((m1_subset_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['125', '126'])).
% 0.51/0.73  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('129', plain,
% 0.51/0.73      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.51/0.73         <= (~
% 0.51/0.73             ((m1_subset_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.51/0.73      inference('clc', [status(thm)], ['127', '128'])).
% 0.51/0.73  thf('130', plain, (~ (v2_struct_0 @ sk_D)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('131', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_C))
% 0.51/0.73         <= (~
% 0.51/0.73             ((m1_subset_1 @ 
% 0.51/0.73               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73               (k1_zfmisc_1 @ 
% 0.51/0.73                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.51/0.73      inference('clc', [status(thm)], ['129', '130'])).
% 0.51/0.73  thf('132', plain, (~ (v2_struct_0 @ sk_C)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('133', plain,
% 0.51/0.73      (((m1_subset_1 @ 
% 0.51/0.73         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73         (k1_zfmisc_1 @ 
% 0.51/0.73          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['131', '132'])).
% 0.51/0.73  thf('134', plain,
% 0.51/0.73      (~
% 0.51/0.73       ((v5_pre_topc @ 
% 0.51/0.73         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)) | 
% 0.51/0.73       ~
% 0.51/0.73       ((m1_subset_1 @ 
% 0.51/0.73         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73         (k1_zfmisc_1 @ 
% 0.51/0.73          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))) | 
% 0.51/0.73       ~
% 0.51/0.73       ((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.51/0.73         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))) | 
% 0.51/0.73       ~
% 0.51/0.73       ((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.51/0.73      inference('split', [status(esa)], ['43'])).
% 0.51/0.73  thf('135', plain,
% 0.51/0.73      (~
% 0.51/0.73       ((v5_pre_topc @ 
% 0.51/0.73         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))),
% 0.51/0.73      inference('sat_resolution*', [status(thm)], ['73', '103', '133', '134'])).
% 0.51/0.73  thf('136', plain,
% 0.51/0.73      (~ (v5_pre_topc @ 
% 0.51/0.73          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)),
% 0.51/0.73      inference('simpl_trail', [status(thm)], ['44', '135'])).
% 0.51/0.73  thf('137', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_B)
% 0.51/0.73        | (v2_struct_0 @ sk_D)
% 0.51/0.73        | (v2_struct_0 @ sk_C)
% 0.51/0.73        | (v2_struct_0 @ sk_A))),
% 0.51/0.73      inference('sup-', [status(thm)], ['42', '136'])).
% 0.51/0.73  thf('138', plain, (~ (v2_struct_0 @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('139', plain,
% 0.51/0.73      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.51/0.73      inference('sup-', [status(thm)], ['137', '138'])).
% 0.51/0.73  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('141', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.51/0.73      inference('clc', [status(thm)], ['139', '140'])).
% 0.51/0.73  thf('142', plain, (~ (v2_struct_0 @ sk_D)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('143', plain, ((v2_struct_0 @ sk_C)),
% 0.51/0.73      inference('clc', [status(thm)], ['141', '142'])).
% 0.51/0.73  thf('144', plain, ($false), inference('demod', [status(thm)], ['0', '143'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
