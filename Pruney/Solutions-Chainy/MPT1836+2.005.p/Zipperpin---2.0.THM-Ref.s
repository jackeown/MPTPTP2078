%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.auSklDVqtE

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:14 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 689 expanded)
%              Number of leaves         :   31 ( 212 expanded)
%              Depth                    :   26
%              Number of atoms          : 3911 (62308 expanded)
%              Number of equality atoms :   10 ( 362 expanded)
%              Maximal formula depth    :   32 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    v1_borsuk_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_borsuk_1 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( r4_tsep_1 @ X25 @ X24 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( v1_borsuk_1 @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t87_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_C @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ sk_A ) ) ),
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
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_borsuk_1 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r4_tsep_1 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r4_tsep_1 @ sk_A @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_C @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_E ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
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

thf('18',plain,(
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

thf('19',plain,(
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
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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
    inference(demod,[status(thm)],['19','20','21','22','23','24'])).

thf('26',plain,
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
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) @ sk_F ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28','29','30','31','34','35','36','37'])).

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

thf('39',plain,(
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

thf('40',plain,
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
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r4_tsep_1 @ sk_A @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['11','12'])).

thf('49',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
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
    inference(demod,[status(thm)],['40','41','42','43','44','45','46','47','48','49','50','51','52','53','54','55','56'])).

thf('58',plain,
    ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
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

thf('64',plain,(
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

thf('65',plain,(
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
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
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
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
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
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
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
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['59'])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
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

thf('94',plain,(
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
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
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
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
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
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
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
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['90','103'])).

thf('105',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['59'])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
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

thf('124',plain,(
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
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
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
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,(
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
    inference('sup-',[status(thm)],['121','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
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
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['120','133'])).

thf('135',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['134','135','136','137','138'])).

thf('140',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['59'])).

thf('151',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['89','119','149','150'])).

thf('152',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['60','151'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
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

thf('156',plain,(
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

thf('157',plain,(
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
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
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
    inference(demod,[status(thm)],['157','158','159','160','161','162'])).

thf('164',plain,(
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
    inference('sup-',[status(thm)],['154','163'])).

thf('165',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
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
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,(
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
    inference('sup-',[status(thm)],['153','168'])).

thf('170',plain,(
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
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
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
    inference('sup-',[status(thm)],['13','170'])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['171','172','173','174','175','176'])).

thf('178',plain,
    ( ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['60','151'])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    $false ),
    inference(demod,[status(thm)],['0','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.auSklDVqtE
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:24:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 379 iterations in 0.499s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.76/0.96  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.76/0.96  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.96  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.76/0.96  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.76/0.96  thf(sk_E_type, type, sk_E: $i).
% 0.76/0.96  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.76/0.96  thf(sk_F_type, type, sk_F: $i).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.96  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.76/0.96  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.96  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.76/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.96  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.76/0.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(t152_tmap_1, conjecture,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.96             ( l1_pre_topc @ B ) ) =>
% 0.76/0.96           ( ![C:$i]:
% 0.76/0.96             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_borsuk_1 @ C @ A ) & 
% 0.76/0.96                 ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.96               ( ![D:$i]:
% 0.76/0.96                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_borsuk_1 @ D @ A ) & 
% 0.76/0.96                     ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.96                   ( ![E:$i]:
% 0.76/0.96                     ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.96                         ( v1_funct_2 @
% 0.76/0.96                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                         ( v5_pre_topc @ E @ C @ B ) & 
% 0.76/0.96                         ( m1_subset_1 @
% 0.76/0.96                           E @ 
% 0.76/0.96                           ( k1_zfmisc_1 @
% 0.76/0.96                             ( k2_zfmisc_1 @
% 0.76/0.96                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.96                       ( ![F:$i]:
% 0.76/0.96                         ( ( ( v1_funct_1 @ F ) & 
% 0.76/0.96                             ( v1_funct_2 @
% 0.76/0.96                               F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                             ( v5_pre_topc @ F @ D @ B ) & 
% 0.76/0.96                             ( m1_subset_1 @
% 0.76/0.96                               F @ 
% 0.76/0.96                               ( k1_zfmisc_1 @
% 0.76/0.96                                 ( k2_zfmisc_1 @
% 0.76/0.96                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.96                           ( ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) & 
% 0.76/0.96                               ( r2_funct_2 @
% 0.76/0.96                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.76/0.96                                 ( k3_tmap_1 @
% 0.76/0.96                                   A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.76/0.96                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.76/0.96                                 E ) & 
% 0.76/0.96                               ( r2_funct_2 @
% 0.76/0.96                                 ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.76/0.96                                 ( k3_tmap_1 @
% 0.76/0.96                                   A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.76/0.96                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.76/0.96                                 F ) ) =>
% 0.76/0.96                             ( ( v1_funct_1 @
% 0.76/0.96                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.76/0.96                               ( v1_funct_2 @
% 0.76/0.96                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.96                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                               ( v5_pre_topc @
% 0.76/0.96                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ A @ B ) & 
% 0.76/0.96                               ( m1_subset_1 @
% 0.76/0.96                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.96                                 ( k1_zfmisc_1 @
% 0.76/0.96                                   ( k2_zfmisc_1 @
% 0.76/0.96                                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i]:
% 0.76/0.96        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.76/0.96            ( l1_pre_topc @ A ) ) =>
% 0.76/0.96          ( ![B:$i]:
% 0.76/0.96            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.96                ( l1_pre_topc @ B ) ) =>
% 0.76/0.96              ( ![C:$i]:
% 0.76/0.96                ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_borsuk_1 @ C @ A ) & 
% 0.76/0.96                    ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.96                  ( ![D:$i]:
% 0.76/0.96                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_borsuk_1 @ D @ A ) & 
% 0.76/0.96                        ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.96                      ( ![E:$i]:
% 0.76/0.96                        ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.96                            ( v1_funct_2 @
% 0.76/0.96                              E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                            ( v5_pre_topc @ E @ C @ B ) & 
% 0.76/0.96                            ( m1_subset_1 @
% 0.76/0.96                              E @ 
% 0.76/0.96                              ( k1_zfmisc_1 @
% 0.76/0.96                                ( k2_zfmisc_1 @
% 0.76/0.96                                  ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.96                          ( ![F:$i]:
% 0.76/0.96                            ( ( ( v1_funct_1 @ F ) & 
% 0.76/0.96                                ( v1_funct_2 @
% 0.76/0.96                                  F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                                ( v5_pre_topc @ F @ D @ B ) & 
% 0.76/0.96                                ( m1_subset_1 @
% 0.76/0.96                                  F @ 
% 0.76/0.96                                  ( k1_zfmisc_1 @
% 0.76/0.96                                    ( k2_zfmisc_1 @
% 0.76/0.96                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.96                              ( ( ( ( A ) = ( k1_tsep_1 @ A @ C @ D ) ) & 
% 0.76/0.96                                  ( r2_funct_2 @
% 0.76/0.96                                    ( u1_struct_0 @ C ) @ 
% 0.76/0.96                                    ( u1_struct_0 @ B ) @ 
% 0.76/0.96                                    ( k3_tmap_1 @
% 0.76/0.96                                      A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.76/0.96                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.76/0.96                                    E ) & 
% 0.76/0.96                                  ( r2_funct_2 @
% 0.76/0.96                                    ( u1_struct_0 @ D ) @ 
% 0.76/0.96                                    ( u1_struct_0 @ B ) @ 
% 0.76/0.96                                    ( k3_tmap_1 @
% 0.76/0.96                                      A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.76/0.96                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.76/0.96                                    F ) ) =>
% 0.76/0.96                                ( ( v1_funct_1 @
% 0.76/0.96                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.76/0.96                                  ( v1_funct_2 @
% 0.76/0.96                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.96                                    ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                                  ( v5_pre_topc @
% 0.76/0.96                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.96                                    A @ B ) & 
% 0.76/0.96                                  ( m1_subset_1 @
% 0.76/0.96                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.96                                    ( k1_zfmisc_1 @
% 0.76/0.96                                      ( k2_zfmisc_1 @
% 0.76/0.96                                        ( u1_struct_0 @ A ) @ 
% 0.76/0.96                                        ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t152_tmap_1])).
% 0.76/0.96  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain, ((v1_borsuk_1 @ sk_D @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('2', plain, ((v1_borsuk_1 @ sk_C @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t87_tsep_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.76/0.96           ( ![C:$i]:
% 0.76/0.96             ( ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.96               ( r4_tsep_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.96         (~ (v1_borsuk_1 @ X24 @ X25)
% 0.76/0.96          | ~ (m1_pre_topc @ X24 @ X25)
% 0.76/0.96          | (r4_tsep_1 @ X25 @ X24 @ X26)
% 0.76/0.96          | ~ (m1_pre_topc @ X26 @ X25)
% 0.76/0.96          | ~ (v1_borsuk_1 @ X26 @ X25)
% 0.76/0.96          | ~ (l1_pre_topc @ X25)
% 0.76/0.96          | ~ (v2_pre_topc @ X25)
% 0.76/0.96          | (v2_struct_0 @ X25))),
% 0.76/0.96      inference('cnf', [status(esa)], [t87_tsep_1])).
% 0.76/0.96  thf('4', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((v2_struct_0 @ sk_A)
% 0.76/0.96          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.96          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.96          | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 0.76/0.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.96          | (r4_tsep_1 @ sk_A @ sk_C @ X0)
% 0.76/0.96          | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.96  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('8', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((v2_struct_0 @ sk_A)
% 0.76/0.96          | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 0.76/0.96          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.76/0.96          | (r4_tsep_1 @ sk_A @ sk_C @ X0))),
% 0.76/0.96      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      (((r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.76/0.96        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.76/0.96        | (v2_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['1', '8'])).
% 0.76/0.96  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('11', plain, (((r4_tsep_1 @ sk_A @ sk_C @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('13', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.76/0.96      inference('clc', [status(thm)], ['11', '12'])).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.96        (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_C @ 
% 0.76/0.96         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.76/0.96        sk_E)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('15', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.96        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ 
% 0.76/0.96         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.76/0.96        sk_E)),
% 0.76/0.96      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/0.96  thf('17', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t140_tmap_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.96             ( l1_pre_topc @ B ) ) =>
% 0.76/0.96           ( ![C:$i]:
% 0.76/0.96             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.96               ( ![D:$i]:
% 0.76/0.96                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.96                   ( ( ~( r1_tsep_1 @ C @ D ) ) =>
% 0.76/0.96                     ( ![E:$i]:
% 0.76/0.96                       ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.96                           ( v1_funct_2 @
% 0.76/0.96                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                           ( m1_subset_1 @
% 0.76/0.96                             E @ 
% 0.76/0.96                             ( k1_zfmisc_1 @
% 0.76/0.96                               ( k2_zfmisc_1 @
% 0.76/0.96                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.96                         ( ![F:$i]:
% 0.76/0.96                           ( ( ( v1_funct_1 @ F ) & 
% 0.76/0.97                               ( v1_funct_2 @
% 0.76/0.97                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.97                               ( m1_subset_1 @
% 0.76/0.97                                 F @ 
% 0.76/0.97                                 ( k1_zfmisc_1 @
% 0.76/0.97                                   ( k2_zfmisc_1 @
% 0.76/0.97                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.97                             ( ( ( r2_funct_2 @
% 0.76/0.97                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.76/0.97                                   ( k3_tmap_1 @
% 0.76/0.97                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ 
% 0.76/0.97                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.76/0.97                                   E ) & 
% 0.76/0.97                                 ( r2_funct_2 @
% 0.76/0.97                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.76/0.97                                   ( k3_tmap_1 @
% 0.76/0.97                                     A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ 
% 0.76/0.97                                     ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) @ 
% 0.76/0.97                                   F ) ) <=>
% 0.76/0.97                               ( r2_funct_2 @
% 0.76/0.97                                 ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.97                                 ( u1_struct_0 @ B ) @ 
% 0.76/0.97                                 ( k3_tmap_1 @
% 0.76/0.97                                   A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ 
% 0.76/0.97                                 ( k3_tmap_1 @
% 0.76/0.97                                   A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X6)
% 0.76/0.97          | ~ (v2_pre_topc @ X6)
% 0.76/0.97          | ~ (l1_pre_topc @ X6)
% 0.76/0.97          | (v2_struct_0 @ X7)
% 0.76/0.97          | ~ (m1_pre_topc @ X7 @ X8)
% 0.76/0.97          | ~ (v1_funct_1 @ X9)
% 0.76/0.97          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 0.76/0.97          | ~ (m1_subset_1 @ X9 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 0.76/0.97          | ~ (r2_funct_2 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6) @ 
% 0.76/0.97               (k3_tmap_1 @ X8 @ X6 @ (k1_tsep_1 @ X8 @ X10 @ X7) @ X10 @ 
% 0.76/0.97                (k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9)) @ 
% 0.76/0.97               X11)
% 0.76/0.97          | ~ (r2_funct_2 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6) @ 
% 0.76/0.97               (k3_tmap_1 @ X8 @ X6 @ (k1_tsep_1 @ X8 @ X10 @ X7) @ X7 @ 
% 0.76/0.97                (k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9)) @ 
% 0.76/0.97               X9)
% 0.76/0.97          | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ X8 @ X10 @ X7)) @ 
% 0.76/0.97             (u1_struct_0 @ X6) @ 
% 0.76/0.97             (k3_tmap_1 @ X8 @ X6 @ X10 @ (k2_tsep_1 @ X8 @ X10 @ X7) @ X11) @ 
% 0.76/0.97             (k3_tmap_1 @ X8 @ X6 @ X7 @ (k2_tsep_1 @ X8 @ X10 @ X7) @ X9))
% 0.76/0.97          | ~ (m1_subset_1 @ X11 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))))
% 0.76/0.97          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))
% 0.76/0.97          | ~ (v1_funct_1 @ X11)
% 0.76/0.97          | (r1_tsep_1 @ X10 @ X7)
% 0.76/0.97          | ~ (m1_pre_topc @ X10 @ X8)
% 0.76/0.97          | (v2_struct_0 @ X10)
% 0.76/0.97          | ~ (l1_pre_topc @ X8)
% 0.76/0.97          | ~ (v2_pre_topc @ X8)
% 0.76/0.97          | (v2_struct_0 @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [t140_tmap_1])).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.76/0.97             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.76/0.97              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1)) @ 
% 0.76/0.97             X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.76/0.97          | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.76/0.97             (u1_struct_0 @ X2) @ 
% 0.76/0.97             (k3_tmap_1 @ sk_A @ X2 @ sk_C @ 
% 0.76/0.97              (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ X0) @ 
% 0.76/0.97             (k3_tmap_1 @ sk_A @ X2 @ sk_D @ 
% 0.76/0.97              (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ X1))
% 0.76/0.97          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.76/0.97               (k3_tmap_1 @ sk_A @ X2 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.76/0.97                sk_D @ (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1)) @ 
% 0.76/0.97               X1)
% 0.76/0.97          | ~ (m1_subset_1 @ X1 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (v1_funct_1 @ X1)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (l1_pre_topc @ X2)
% 0.76/0.97          | ~ (v2_pre_topc @ X2)
% 0.76/0.97          | (v2_struct_0 @ X2))),
% 0.76/0.97      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.97  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('23', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2) @ 
% 0.76/0.97             (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_C @ 
% 0.76/0.97              (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1)) @ 
% 0.76/0.97             X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.76/0.97             (u1_struct_0 @ X2) @ 
% 0.76/0.97             (k3_tmap_1 @ sk_A @ X2 @ sk_C @ 
% 0.76/0.97              (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ X0) @ 
% 0.76/0.97             (k3_tmap_1 @ sk_A @ X2 @ sk_D @ 
% 0.76/0.97              (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ X1))
% 0.76/0.97          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2) @ 
% 0.76/0.97               (k3_tmap_1 @ sk_A @ X2 @ sk_A @ sk_D @ 
% 0.76/0.97                (k10_tmap_1 @ sk_A @ X2 @ sk_C @ sk_D @ X0 @ X1)) @ 
% 0.76/0.97               X1)
% 0.76/0.97          | ~ (m1_subset_1 @ X1 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (v1_funct_1 @ X1)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (l1_pre_topc @ X2)
% 0.76/0.97          | ~ (v2_pre_topc @ X2)
% 0.76/0.97          | (v2_struct_0 @ X2))),
% 0.76/0.97      inference('demod', [status(thm)], ['19', '20', '21', '22', '23', '24'])).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_B)
% 0.76/0.97        | ~ (v2_pre_topc @ sk_B)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_F)
% 0.76/0.97        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.97        | ~ (m1_subset_1 @ sk_F @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.97             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.76/0.97              (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.76/0.97             sk_F)
% 0.76/0.97        | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.76/0.97           (u1_struct_0 @ sk_B) @ 
% 0.76/0.97           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 0.76/0.97            (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_E) @ 
% 0.76/0.97           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ 
% 0.76/0.97            (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_F))
% 0.76/0.97        | ~ (m1_subset_1 @ sk_E @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.97        | ~ (v1_funct_1 @ sk_E)
% 0.76/0.97        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['16', '25'])).
% 0.76/0.97  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('28', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('29', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_F @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.97        (k3_tmap_1 @ sk_A @ sk_B @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_D @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.76/0.97        sk_F)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('33', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      ((r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.76/0.97        (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)) @ 
% 0.76/0.97        sk_F)),
% 0.76/0.97      inference('demod', [status(thm)], ['32', '33'])).
% 0.76/0.97  thf('35', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_E @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('37', plain, ((v1_funct_1 @ sk_E)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('38', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.76/0.97           (u1_struct_0 @ sk_B) @ 
% 0.76/0.97           (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ 
% 0.76/0.97            (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_E) @ 
% 0.76/0.97           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ 
% 0.76/0.97            (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_F))
% 0.76/0.97        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['26', '27', '28', '29', '30', '31', '34', '35', '36', '37'])).
% 0.76/0.97  thf(t144_tmap_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.97             ( l1_pre_topc @ B ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.97               ( ![D:$i]:
% 0.76/0.97                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.97                   ( ( ~( r1_tsep_1 @ C @ D ) ) =>
% 0.76/0.97                     ( ![E:$i]:
% 0.76/0.97                       ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.97                           ( v1_funct_2 @
% 0.76/0.97                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.97                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.76/0.97                           ( m1_subset_1 @
% 0.76/0.97                             E @ 
% 0.76/0.97                             ( k1_zfmisc_1 @
% 0.76/0.97                               ( k2_zfmisc_1 @
% 0.76/0.97                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.97                         ( ![F:$i]:
% 0.76/0.97                           ( ( ( v1_funct_1 @ F ) & 
% 0.76/0.97                               ( v1_funct_2 @
% 0.76/0.97                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.97                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.76/0.97                               ( m1_subset_1 @
% 0.76/0.97                                 F @ 
% 0.76/0.97                                 ( k1_zfmisc_1 @
% 0.76/0.97                                   ( k2_zfmisc_1 @
% 0.76/0.97                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.97                             ( ( ( r2_funct_2 @
% 0.76/0.97                                   ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.97                                   ( u1_struct_0 @ B ) @ 
% 0.76/0.97                                   ( k3_tmap_1 @
% 0.76/0.97                                     A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ 
% 0.76/0.97                                   ( k3_tmap_1 @
% 0.76/0.97                                     A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) & 
% 0.76/0.97                                 ( r4_tsep_1 @ A @ C @ D ) ) =>
% 0.76/0.97                               ( ( v1_funct_1 @
% 0.76/0.97                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.76/0.97                                 ( v1_funct_2 @
% 0.76/0.97                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.97                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.97                                   ( u1_struct_0 @ B ) ) & 
% 0.76/0.97                                 ( v5_pre_topc @
% 0.76/0.97                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.97                                   ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.76/0.97                                 ( m1_subset_1 @
% 0.76/0.97                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.97                                   ( k1_zfmisc_1 @
% 0.76/0.97                                     ( k2_zfmisc_1 @
% 0.76/0.97                                       ( u1_struct_0 @
% 0.76/0.97                                         ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.97                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('39', plain,
% 0.76/0.97      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X12)
% 0.76/0.97          | ~ (v2_pre_topc @ X12)
% 0.76/0.97          | ~ (l1_pre_topc @ X12)
% 0.76/0.97          | (v2_struct_0 @ X13)
% 0.76/0.97          | ~ (m1_pre_topc @ X13 @ X14)
% 0.76/0.97          | ~ (v1_funct_1 @ X15)
% 0.76/0.97          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.76/0.97          | ~ (v5_pre_topc @ X15 @ X13 @ X12)
% 0.76/0.97          | ~ (m1_subset_1 @ X15 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))))
% 0.76/0.97          | (v5_pre_topc @ (k10_tmap_1 @ X14 @ X12 @ X16 @ X13 @ X17 @ X15) @ 
% 0.76/0.97             (k1_tsep_1 @ X14 @ X16 @ X13) @ X12)
% 0.76/0.97          | ~ (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ X14 @ X16 @ X13)) @ 
% 0.76/0.97               (u1_struct_0 @ X12) @ 
% 0.76/0.97               (k3_tmap_1 @ X14 @ X12 @ X16 @ (k2_tsep_1 @ X14 @ X16 @ X13) @ 
% 0.76/0.97                X17) @ 
% 0.76/0.97               (k3_tmap_1 @ X14 @ X12 @ X13 @ (k2_tsep_1 @ X14 @ X16 @ X13) @ 
% 0.76/0.97                X15))
% 0.76/0.97          | ~ (r4_tsep_1 @ X14 @ X16 @ X13)
% 0.76/0.97          | ~ (m1_subset_1 @ X17 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X12))))
% 0.76/0.97          | ~ (v5_pre_topc @ X17 @ X16 @ X12)
% 0.76/0.97          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X12))
% 0.76/0.97          | ~ (v1_funct_1 @ X17)
% 0.76/0.97          | (r1_tsep_1 @ X16 @ X13)
% 0.76/0.97          | ~ (m1_pre_topc @ X16 @ X14)
% 0.76/0.97          | (v2_struct_0 @ X16)
% 0.76/0.97          | ~ (l1_pre_topc @ X14)
% 0.76/0.97          | ~ (v2_pre_topc @ X14)
% 0.76/0.97          | (v2_struct_0 @ X14))),
% 0.76/0.97      inference('cnf', [status(esa)], [t144_tmap_1])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.76/0.97        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_E)
% 0.76/0.97        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.97        | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.76/0.97        | ~ (m1_subset_1 @ sk_E @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.76/0.97        | (v5_pre_topc @ 
% 0.76/0.97           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.76/0.97        | ~ (m1_subset_1 @ sk_F @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97        | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.76/0.97        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.97        | ~ (v1_funct_1 @ sk_F)
% 0.76/0.97        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_B)
% 0.76/0.97        | ~ (v2_pre_topc @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.97  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('43', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('44', plain, ((v1_funct_1 @ sk_E)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('46', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('47', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_E @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('48', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.76/0.97      inference('clc', [status(thm)], ['11', '12'])).
% 0.76/0.97  thf('49', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('50', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_F @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('51', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('52', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('53', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('54', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('56', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('57', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97        | (v5_pre_topc @ 
% 0.76/0.97           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['40', '41', '42', '43', '44', '45', '46', '47', '48', '49', 
% 0.76/0.97                 '50', '51', '52', '53', '54', '55', '56'])).
% 0.76/0.97  thf('58', plain,
% 0.76/0.97      (((v5_pre_topc @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('simplify', [status(thm)], ['57'])).
% 0.76/0.97  thf('59', plain,
% 0.76/0.97      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.76/0.97        | ~ (v1_funct_2 @ 
% 0.76/0.97             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.97        | ~ (v5_pre_topc @ 
% 0.76/0.97             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.76/0.97             sk_B)
% 0.76/0.97        | ~ (m1_subset_1 @ 
% 0.76/0.97             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('60', plain,
% 0.76/0.97      ((~ (v5_pre_topc @ 
% 0.76/0.97           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v5_pre_topc @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ 
% 0.76/0.97               sk_B)))),
% 0.76/0.97      inference('split', [status(esa)], ['59'])).
% 0.76/0.97  thf('61', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('62', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_F @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('63', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_E @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(dt_k10_tmap_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.76/0.97         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.76/0.97         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 0.76/0.97         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.76/0.97         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 0.76/0.97         ( v1_funct_1 @ E ) & 
% 0.76/0.97         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.97         ( m1_subset_1 @
% 0.76/0.97           E @ 
% 0.76/0.97           ( k1_zfmisc_1 @
% 0.76/0.97             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.76/0.97         ( v1_funct_1 @ F ) & 
% 0.76/0.97         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.97         ( m1_subset_1 @
% 0.76/0.97           F @ 
% 0.76/0.97           ( k1_zfmisc_1 @
% 0.76/0.97             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.97       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.76/0.97         ( v1_funct_2 @
% 0.76/0.97           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.97           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.97         ( m1_subset_1 @
% 0.76/0.97           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.97           ( k1_zfmisc_1 @
% 0.76/0.97             ( k2_zfmisc_1 @
% 0.76/0.97               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.97               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.76/0.97  thf('64', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (m1_pre_topc @ X3 @ X4)
% 0.76/0.97          | (v2_struct_0 @ X3)
% 0.76/0.97          | ~ (m1_pre_topc @ X1 @ X4)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (l1_pre_topc @ X2)
% 0.76/0.97          | ~ (v2_pre_topc @ X2)
% 0.76/0.97          | (v2_struct_0 @ X2)
% 0.76/0.97          | ~ (l1_pre_topc @ X4)
% 0.76/0.97          | ~ (v2_pre_topc @ X4)
% 0.76/0.97          | (v2_struct_0 @ X4)
% 0.76/0.97          | ~ (v1_funct_1 @ X5)
% 0.76/0.97          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (m1_subset_1 @ X5 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | (v1_funct_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.76/0.97  thf('65', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | (v2_struct_0 @ X2)
% 0.76/0.97          | ~ (v2_pre_topc @ X2)
% 0.76/0.97          | ~ (l1_pre_topc @ X2)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (m1_pre_topc @ X1 @ X2)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_E)
% 0.76/0.97          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['63', '64'])).
% 0.76/0.97  thf('66', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('67', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('69', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('70', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.76/0.97          | ~ (m1_subset_1 @ X0 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | (v2_struct_0 @ X2)
% 0.76/0.97          | ~ (v2_pre_topc @ X2)
% 0.76/0.97          | ~ (l1_pre_topc @ X2)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (m1_pre_topc @ X1 @ X2))),
% 0.76/0.97      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.76/0.97  thf('71', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.97          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['62', '70'])).
% 0.76/0.97  thf('72', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('73', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('74', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.76/0.97      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.76/0.97  thf('75', plain,
% 0.76/0.97      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_D))),
% 0.76/0.97      inference('sup-', [status(thm)], ['61', '74'])).
% 0.76/0.97  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('78', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('79', plain,
% 0.76/0.97      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_D))),
% 0.76/0.97      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.76/0.97  thf('80', plain,
% 0.76/0.97      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.76/0.97      inference('split', [status(esa)], ['59'])).
% 0.76/0.97  thf('81', plain,
% 0.76/0.97      ((((v2_struct_0 @ sk_D)
% 0.76/0.97         | (v2_struct_0 @ sk_C)
% 0.76/0.97         | (v2_struct_0 @ sk_B)
% 0.76/0.97         | (v2_struct_0 @ sk_A)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['79', '80'])).
% 0.76/0.97  thf('82', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('83', plain,
% 0.76/0.97      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['81', '82'])).
% 0.76/0.97  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('85', plain,
% 0.76/0.97      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.76/0.97      inference('clc', [status(thm)], ['83', '84'])).
% 0.76/0.97  thf('86', plain, (~ (v2_struct_0 @ sk_D)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('87', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_C))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.76/0.97      inference('clc', [status(thm)], ['85', '86'])).
% 0.76/0.97  thf('88', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('89', plain,
% 0.76/0.97      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['87', '88'])).
% 0.76/0.97  thf('90', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('91', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_F @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('92', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_E @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('93', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (m1_pre_topc @ X3 @ X4)
% 0.76/0.97          | (v2_struct_0 @ X3)
% 0.76/0.97          | ~ (m1_pre_topc @ X1 @ X4)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (l1_pre_topc @ X2)
% 0.76/0.97          | ~ (v2_pre_topc @ X2)
% 0.76/0.97          | (v2_struct_0 @ X2)
% 0.76/0.97          | ~ (l1_pre_topc @ X4)
% 0.76/0.97          | ~ (v2_pre_topc @ X4)
% 0.76/0.97          | (v2_struct_0 @ X4)
% 0.76/0.97          | ~ (v1_funct_1 @ X5)
% 0.76/0.97          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (m1_subset_1 @ X5 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | (v1_funct_2 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.76/0.97             (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ (u1_struct_0 @ X2)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.76/0.97  thf('94', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.76/0.97           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (m1_subset_1 @ X2 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v1_funct_1 @ X2)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (v2_pre_topc @ X1)
% 0.76/0.97          | ~ (l1_pre_topc @ X1)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | ~ (m1_pre_topc @ X0 @ X1)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_E)
% 0.76/0.97          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['92', '93'])).
% 0.76/0.97  thf('95', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('97', plain, ((v1_funct_1 @ sk_E)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('98', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('99', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.76/0.97           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (m1_subset_1 @ X2 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v1_funct_1 @ X2)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (v2_pre_topc @ X1)
% 0.76/0.97          | ~ (l1_pre_topc @ X1)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.76/0.97      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.76/0.97  thf('100', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.97          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | (v1_funct_2 @ 
% 0.76/0.97             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.76/0.97             (u1_struct_0 @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['91', '99'])).
% 0.76/0.97  thf('101', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('102', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('103', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | (v1_funct_2 @ 
% 0.76/0.97             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.76/0.97             (u1_struct_0 @ sk_B)))),
% 0.76/0.97      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.76/0.97  thf('104', plain,
% 0.76/0.97      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.76/0.97         (u1_struct_0 @ sk_B))
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_D))),
% 0.76/0.97      inference('sup-', [status(thm)], ['90', '103'])).
% 0.76/0.97  thf('105', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('108', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('109', plain,
% 0.76/0.97      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_D))),
% 0.76/0.97      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.76/0.97  thf('110', plain,
% 0.76/0.97      ((~ (v1_funct_2 @ 
% 0.76/0.97           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_2 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('split', [status(esa)], ['59'])).
% 0.76/0.97  thf('111', plain,
% 0.76/0.97      ((((v2_struct_0 @ sk_D)
% 0.76/0.97         | (v2_struct_0 @ sk_C)
% 0.76/0.97         | (v2_struct_0 @ sk_B)
% 0.76/0.97         | (v2_struct_0 @ sk_A)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_2 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['109', '110'])).
% 0.76/0.97  thf('112', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('113', plain,
% 0.76/0.97      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_2 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['111', '112'])).
% 0.76/0.97  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('115', plain,
% 0.76/0.97      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_2 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('clc', [status(thm)], ['113', '114'])).
% 0.76/0.97  thf('116', plain, (~ (v2_struct_0 @ sk_D)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('117', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_C))
% 0.76/0.97         <= (~
% 0.76/0.97             ((v1_funct_2 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('clc', [status(thm)], ['115', '116'])).
% 0.76/0.97  thf('118', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('119', plain,
% 0.76/0.97      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['117', '118'])).
% 0.76/0.97  thf('120', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('121', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_F @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('122', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_E @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('123', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X0 @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (m1_pre_topc @ X3 @ X4)
% 0.76/0.97          | (v2_struct_0 @ X3)
% 0.76/0.97          | ~ (m1_pre_topc @ X1 @ X4)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (l1_pre_topc @ X2)
% 0.76/0.97          | ~ (v2_pre_topc @ X2)
% 0.76/0.97          | (v2_struct_0 @ X2)
% 0.76/0.97          | ~ (l1_pre_topc @ X4)
% 0.76/0.97          | ~ (v2_pre_topc @ X4)
% 0.76/0.97          | (v2_struct_0 @ X4)
% 0.76/0.97          | ~ (v1_funct_1 @ X5)
% 0.76/0.97          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.76/0.97          | ~ (m1_subset_1 @ X5 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.76/0.97          | (m1_subset_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ 
% 0.76/0.97               (u1_struct_0 @ X2)))))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.76/0.97  thf('124', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.76/0.97           (k1_zfmisc_1 @ 
% 0.76/0.97            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.76/0.97             (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (m1_subset_1 @ X2 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v1_funct_1 @ X2)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (v2_pre_topc @ X1)
% 0.76/0.97          | ~ (l1_pre_topc @ X1)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | ~ (m1_pre_topc @ X0 @ X1)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_E)
% 0.76/0.97          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['122', '123'])).
% 0.76/0.97  thf('125', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('126', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('127', plain, ((v1_funct_1 @ sk_E)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('128', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('129', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.76/0.97           (k1_zfmisc_1 @ 
% 0.76/0.97            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.76/0.97             (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (m1_subset_1 @ X2 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v1_funct_1 @ X2)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (v2_pre_topc @ X1)
% 0.76/0.97          | ~ (l1_pre_topc @ X1)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.76/0.97      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 0.76/0.97  thf('130', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.97          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | (m1_subset_1 @ 
% 0.76/0.97             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.76/0.97               (u1_struct_0 @ sk_B)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['121', '129'])).
% 0.76/0.97  thf('131', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('132', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('133', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | (v2_struct_0 @ sk_B)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | (m1_subset_1 @ 
% 0.76/0.97             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (k1_zfmisc_1 @ 
% 0.76/0.97              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.76/0.97               (u1_struct_0 @ sk_B)))))),
% 0.76/0.97      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.76/0.97  thf('134', plain,
% 0.76/0.97      (((m1_subset_1 @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97         (k1_zfmisc_1 @ 
% 0.76/0.97          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.76/0.97           (u1_struct_0 @ sk_B))))
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_D))),
% 0.76/0.97      inference('sup-', [status(thm)], ['120', '133'])).
% 0.76/0.97  thf('135', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('136', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('138', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('139', plain,
% 0.76/0.97      (((m1_subset_1 @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97         (k1_zfmisc_1 @ 
% 0.76/0.97          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_D))),
% 0.76/0.97      inference('demod', [status(thm)], ['134', '135', '136', '137', '138'])).
% 0.76/0.97  thf('140', plain,
% 0.76/0.97      ((~ (m1_subset_1 @ 
% 0.76/0.97           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97           (k1_zfmisc_1 @ 
% 0.76/0.97            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))
% 0.76/0.97         <= (~
% 0.76/0.97             ((m1_subset_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.76/0.97      inference('split', [status(esa)], ['59'])).
% 0.76/0.97  thf('141', plain,
% 0.76/0.97      ((((v2_struct_0 @ sk_D)
% 0.76/0.97         | (v2_struct_0 @ sk_C)
% 0.76/0.97         | (v2_struct_0 @ sk_B)
% 0.76/0.97         | (v2_struct_0 @ sk_A)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((m1_subset_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['139', '140'])).
% 0.76/0.97  thf('142', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('143', plain,
% 0.76/0.97      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((m1_subset_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['141', '142'])).
% 0.76/0.97  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('145', plain,
% 0.76/0.97      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.76/0.97         <= (~
% 0.76/0.97             ((m1_subset_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.76/0.97      inference('clc', [status(thm)], ['143', '144'])).
% 0.76/0.97  thf('146', plain, (~ (v2_struct_0 @ sk_D)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('147', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_C))
% 0.76/0.97         <= (~
% 0.76/0.97             ((m1_subset_1 @ 
% 0.76/0.97               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))))),
% 0.76/0.97      inference('clc', [status(thm)], ['145', '146'])).
% 0.76/0.97  thf('148', plain, (~ (v2_struct_0 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('149', plain,
% 0.76/0.97      (((m1_subset_1 @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97         (k1_zfmisc_1 @ 
% 0.76/0.97          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['147', '148'])).
% 0.76/0.97  thf('150', plain,
% 0.76/0.97      (~
% 0.76/0.97       ((v5_pre_topc @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)) | 
% 0.76/0.97       ~
% 0.76/0.97       ((m1_subset_1 @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97         (k1_zfmisc_1 @ 
% 0.76/0.97          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))) | 
% 0.76/0.97       ~
% 0.76/0.97       ((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))) | 
% 0.76/0.97       ~
% 0.76/0.97       ((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.76/0.97      inference('split', [status(esa)], ['59'])).
% 0.76/0.97  thf('151', plain,
% 0.76/0.97      (~
% 0.76/0.97       ((v5_pre_topc @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['89', '119', '149', '150'])).
% 0.76/0.97  thf('152', plain,
% 0.76/0.97      (~ (v5_pre_topc @ 
% 0.76/0.97          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['60', '151'])).
% 0.76/0.97  thf('153', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['58', '152'])).
% 0.76/0.97  thf('154', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_E @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('155', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_F @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t145_tmap_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.76/0.97             ( l1_pre_topc @ B ) ) =>
% 0.76/0.97           ( ![C:$i]:
% 0.76/0.97             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.76/0.97               ( ![D:$i]:
% 0.76/0.97                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.76/0.97                   ( ( r1_tsep_1 @ C @ D ) =>
% 0.76/0.97                     ( ![E:$i]:
% 0.76/0.97                       ( ( ( v1_funct_1 @ E ) & 
% 0.76/0.97                           ( v1_funct_2 @
% 0.76/0.97                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.97                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.76/0.97                           ( m1_subset_1 @
% 0.76/0.97                             E @ 
% 0.76/0.97                             ( k1_zfmisc_1 @
% 0.76/0.97                               ( k2_zfmisc_1 @
% 0.76/0.97                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.97                         ( ![F:$i]:
% 0.76/0.97                           ( ( ( v1_funct_1 @ F ) & 
% 0.76/0.97                               ( v1_funct_2 @
% 0.76/0.97                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.97                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.76/0.97                               ( m1_subset_1 @
% 0.76/0.97                                 F @ 
% 0.76/0.97                                 ( k1_zfmisc_1 @
% 0.76/0.97                                   ( k2_zfmisc_1 @
% 0.76/0.97                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.97                             ( ( r4_tsep_1 @ A @ C @ D ) =>
% 0.76/0.97                               ( ( v1_funct_1 @
% 0.76/0.97                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.76/0.97                                 ( v1_funct_2 @
% 0.76/0.97                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.97                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.97                                   ( u1_struct_0 @ B ) ) & 
% 0.76/0.97                                 ( v5_pre_topc @
% 0.76/0.97                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.97                                   ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.76/0.97                                 ( m1_subset_1 @
% 0.76/0.97                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.76/0.97                                   ( k1_zfmisc_1 @
% 0.76/0.97                                     ( k2_zfmisc_1 @
% 0.76/0.97                                       ( u1_struct_0 @
% 0.76/0.97                                         ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.76/0.97                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf('156', plain,
% 0.76/0.97      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X18)
% 0.76/0.97          | ~ (v2_pre_topc @ X18)
% 0.76/0.97          | ~ (l1_pre_topc @ X18)
% 0.76/0.97          | (v2_struct_0 @ X19)
% 0.76/0.97          | ~ (m1_pre_topc @ X19 @ X20)
% 0.76/0.97          | ~ (v1_funct_1 @ X21)
% 0.76/0.97          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.76/0.97          | ~ (v5_pre_topc @ X21 @ X19 @ X18)
% 0.76/0.97          | ~ (m1_subset_1 @ X21 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))))
% 0.76/0.97          | (v5_pre_topc @ (k10_tmap_1 @ X20 @ X18 @ X22 @ X19 @ X23 @ X21) @ 
% 0.76/0.97             (k1_tsep_1 @ X20 @ X22 @ X19) @ X18)
% 0.76/0.97          | ~ (r4_tsep_1 @ X20 @ X22 @ X19)
% 0.76/0.97          | ~ (m1_subset_1 @ X23 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X18))))
% 0.76/0.97          | ~ (v5_pre_topc @ X23 @ X22 @ X18)
% 0.76/0.97          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X18))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (r1_tsep_1 @ X22 @ X19)
% 0.76/0.97          | ~ (m1_pre_topc @ X22 @ X20)
% 0.76/0.97          | (v2_struct_0 @ X22)
% 0.76/0.97          | ~ (l1_pre_topc @ X20)
% 0.76/0.97          | ~ (v2_pre_topc @ X20)
% 0.76/0.97          | (v2_struct_0 @ X20))),
% 0.76/0.97      inference('cnf', [status(esa)], [t145_tmap_1])).
% 0.76/0.97  thf('157', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.97          | ~ (r1_tsep_1 @ X1 @ sk_D)
% 0.76/0.97          | ~ (v1_funct_1 @ X2)
% 0.76/0.97          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v5_pre_topc @ X2 @ X1 @ sk_B)
% 0.76/0.97          | ~ (m1_subset_1 @ X2 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (r4_tsep_1 @ X0 @ X1 @ sk_D)
% 0.76/0.97          | (v5_pre_topc @ (k10_tmap_1 @ X0 @ sk_B @ X1 @ sk_D @ X2 @ sk_F) @ 
% 0.76/0.97             (k1_tsep_1 @ X0 @ X1 @ sk_D) @ sk_B)
% 0.76/0.97          | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.76/0.97          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v1_funct_1 @ sk_F)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (l1_pre_topc @ sk_B)
% 0.76/0.97          | ~ (v2_pre_topc @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['155', '156'])).
% 0.76/0.97  thf('158', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('159', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('160', plain, ((v1_funct_1 @ sk_F)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('161', plain, ((l1_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('162', plain, ((v2_pre_topc @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('163', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v2_struct_0 @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X1)
% 0.76/0.97          | ~ (m1_pre_topc @ X1 @ X0)
% 0.76/0.97          | ~ (r1_tsep_1 @ X1 @ sk_D)
% 0.76/0.97          | ~ (v1_funct_1 @ X2)
% 0.76/0.97          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v5_pre_topc @ X2 @ X1 @ sk_B)
% 0.76/0.97          | ~ (m1_subset_1 @ X2 @ 
% 0.76/0.97               (k1_zfmisc_1 @ 
% 0.76/0.97                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.76/0.97          | ~ (r4_tsep_1 @ X0 @ X1 @ sk_D)
% 0.76/0.97          | (v5_pre_topc @ (k10_tmap_1 @ X0 @ sk_B @ X1 @ sk_D @ X2 @ sk_F) @ 
% 0.76/0.97             (k1_tsep_1 @ X0 @ X1 @ sk_D) @ sk_B)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['157', '158', '159', '160', '161', '162'])).
% 0.76/0.97  thf('164', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v5_pre_topc @ 
% 0.76/0.97             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.76/0.97          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.76/0.97          | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.76/0.97          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.76/0.97          | ~ (v1_funct_1 @ sk_E)
% 0.76/0.97          | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['154', '163'])).
% 0.76/0.97  thf('165', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('166', plain,
% 0.76/0.97      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('167', plain, ((v1_funct_1 @ sk_E)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('168', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v5_pre_topc @ 
% 0.76/0.97             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.76/0.97          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.76/0.97          | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 0.76/0.97  thf('169', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v2_struct_0 @ sk_B)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.76/0.97          | (v5_pre_topc @ 
% 0.76/0.97             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['153', '168'])).
% 0.76/0.97  thf('170', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (m1_pre_topc @ sk_D @ X0)
% 0.76/0.97          | (v5_pre_topc @ 
% 0.76/0.97             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.76/0.97          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.76/0.97          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.76/0.97          | ~ (l1_pre_topc @ X0)
% 0.76/0.97          | ~ (v2_pre_topc @ X0)
% 0.76/0.97          | (v2_struct_0 @ X0)
% 0.76/0.97          | (v2_struct_0 @ sk_A)
% 0.76/0.97          | (v2_struct_0 @ sk_C)
% 0.76/0.97          | (v2_struct_0 @ sk_D)
% 0.76/0.97          | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['169'])).
% 0.76/0.97  thf('171', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | ~ (v2_pre_topc @ sk_A)
% 0.76/0.97        | ~ (l1_pre_topc @ sk_A)
% 0.76/0.97        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.76/0.97        | (v5_pre_topc @ 
% 0.76/0.97           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.76/0.97           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.76/0.97        | ~ (m1_pre_topc @ sk_D @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['13', '170'])).
% 0.76/0.97  thf('172', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('174', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('175', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_C @ sk_D))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('176', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('177', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | (v5_pre_topc @ 
% 0.76/0.97           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['171', '172', '173', '174', '175', '176'])).
% 0.76/0.97  thf('178', plain,
% 0.76/0.97      (((v5_pre_topc @ 
% 0.76/0.97         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_A)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_B))),
% 0.76/0.97      inference('simplify', [status(thm)], ['177'])).
% 0.76/0.97  thf('179', plain,
% 0.76/0.97      (~ (v5_pre_topc @ 
% 0.76/0.97          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_A @ sk_B)),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['60', '151'])).
% 0.76/0.97  thf('180', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_B)
% 0.76/0.97        | (v2_struct_0 @ sk_D)
% 0.76/0.97        | (v2_struct_0 @ sk_C)
% 0.76/0.97        | (v2_struct_0 @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['178', '179'])).
% 0.76/0.97  thf('181', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('182', plain,
% 0.76/0.97      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.76/0.97      inference('sup-', [status(thm)], ['180', '181'])).
% 0.76/0.97  thf('183', plain, (~ (v2_struct_0 @ sk_A)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('184', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.76/0.97      inference('clc', [status(thm)], ['182', '183'])).
% 0.76/0.97  thf('185', plain, (~ (v2_struct_0 @ sk_D)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('186', plain, ((v2_struct_0 @ sk_C)),
% 0.76/0.97      inference('clc', [status(thm)], ['184', '185'])).
% 0.76/0.97  thf('187', plain, ($false), inference('demod', [status(thm)], ['0', '186'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
