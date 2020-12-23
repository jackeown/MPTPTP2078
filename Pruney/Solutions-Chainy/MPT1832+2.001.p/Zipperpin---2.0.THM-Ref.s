%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yon40Xow5V

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:12 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 325 expanded)
%              Number of leaves         :   26 ( 106 expanded)
%              Depth                    :   20
%              Number of atoms          : 2556 (22300 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   32 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

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

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_tmap_1_type,type,(
    k10_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t148_tmap_1,conjecture,(
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
                           => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                              & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                              & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                             => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                                & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_tmap_1])).

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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
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
      | ( v5_pre_topc @ ( k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9 ) @ ( k1_tsep_1 @ X8 @ X10 @ X7 ) @ X6 )
      | ~ ( r4_tsep_1 @ X8 @ X10 @ X7 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v5_pre_topc @ X11 @ X10 @ X6 )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r1_tsep_1 @ X10 @ X7 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t145_tmap_1])).

thf('17',plain,(
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
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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
    inference(demod,[status(thm)],['17','18','19','20','21','22'])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tsep_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ X0 @ sk_C @ sk_D ) @ sk_B )
      | ~ ( r4_tsep_1 @ X0 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
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

thf('42',plain,(
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
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
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

thf('71',plain,(
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
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
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
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
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
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
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
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
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

thf('100',plain,(
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
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
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
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,(
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
    inference('sup-',[status(thm)],['97','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
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
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['96','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['36'])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('126',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['66','95','124','125'])).

thf('127',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['37','126'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['0','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yon40Xow5V
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 111 iterations in 0.110s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.39/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.57  thf(t148_tmap_1, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.57             ( l1_pre_topc @ B ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_borsuk_1 @ C @ A ) & 
% 0.39/0.57                 ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.57               ( ![D:$i]:
% 0.39/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_borsuk_1 @ D @ A ) & 
% 0.39/0.57                     ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.57                   ( ( r1_tsep_1 @ C @ D ) =>
% 0.39/0.57                     ( ![E:$i]:
% 0.39/0.57                       ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                           ( v1_funct_2 @
% 0.39/0.57                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.39/0.57                           ( m1_subset_1 @
% 0.39/0.57                             E @ 
% 0.39/0.57                             ( k1_zfmisc_1 @
% 0.39/0.57                               ( k2_zfmisc_1 @
% 0.39/0.57                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                         ( ![F:$i]:
% 0.39/0.57                           ( ( ( v1_funct_1 @ F ) & 
% 0.39/0.57                               ( v1_funct_2 @
% 0.39/0.57                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.39/0.57                               ( m1_subset_1 @
% 0.39/0.57                                 F @ 
% 0.39/0.57                                 ( k1_zfmisc_1 @
% 0.39/0.57                                   ( k2_zfmisc_1 @
% 0.39/0.57                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                             ( ( v1_funct_1 @
% 0.39/0.57                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.39/0.57                               ( v1_funct_2 @
% 0.39/0.57                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57                                 ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.39/0.57                                 ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                               ( v5_pre_topc @
% 0.39/0.57                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57                                 ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.39/0.57                               ( m1_subset_1 @
% 0.39/0.57                                 ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57                                 ( k1_zfmisc_1 @
% 0.39/0.57                                   ( k2_zfmisc_1 @
% 0.39/0.57                                     ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.39/0.57                                     ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.57            ( l1_pre_topc @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.57                ( l1_pre_topc @ B ) ) =>
% 0.39/0.57              ( ![C:$i]:
% 0.39/0.57                ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_borsuk_1 @ C @ A ) & 
% 0.39/0.57                    ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.57                  ( ![D:$i]:
% 0.39/0.57                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_borsuk_1 @ D @ A ) & 
% 0.39/0.57                        ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.57                      ( ( r1_tsep_1 @ C @ D ) =>
% 0.39/0.57                        ( ![E:$i]:
% 0.39/0.57                          ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                              ( v1_funct_2 @
% 0.39/0.57                                E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                              ( v5_pre_topc @ E @ C @ B ) & 
% 0.39/0.57                              ( m1_subset_1 @
% 0.39/0.57                                E @ 
% 0.39/0.57                                ( k1_zfmisc_1 @
% 0.39/0.57                                  ( k2_zfmisc_1 @
% 0.39/0.57                                    ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                            ( ![F:$i]:
% 0.39/0.57                              ( ( ( v1_funct_1 @ F ) & 
% 0.39/0.57                                  ( v1_funct_2 @
% 0.39/0.57                                    F @ ( u1_struct_0 @ D ) @ 
% 0.39/0.57                                    ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                                  ( v5_pre_topc @ F @ D @ B ) & 
% 0.39/0.57                                  ( m1_subset_1 @
% 0.39/0.57                                    F @ 
% 0.39/0.57                                    ( k1_zfmisc_1 @
% 0.39/0.57                                      ( k2_zfmisc_1 @
% 0.39/0.57                                        ( u1_struct_0 @ D ) @ 
% 0.39/0.57                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                                ( ( v1_funct_1 @
% 0.39/0.57                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.39/0.57                                  ( v1_funct_2 @
% 0.39/0.57                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57                                    ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.39/0.57                                    ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                                  ( v5_pre_topc @
% 0.39/0.57                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57                                    ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.39/0.57                                  ( m1_subset_1 @
% 0.39/0.57                                    ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57                                    ( k1_zfmisc_1 @
% 0.39/0.57                                      ( k2_zfmisc_1 @
% 0.39/0.57                                        ( u1_struct_0 @
% 0.39/0.57                                          ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.39/0.57                                        ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t148_tmap_1])).
% 0.39/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, ((v1_borsuk_1 @ sk_D @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('2', plain, ((v1_borsuk_1 @ sk_C @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t87_tsep_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.57               ( r4_tsep_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (v1_borsuk_1 @ X12 @ X13)
% 0.39/0.57          | ~ (m1_pre_topc @ X12 @ X13)
% 0.39/0.57          | (r4_tsep_1 @ X13 @ X12 @ X14)
% 0.39/0.57          | ~ (m1_pre_topc @ X14 @ X13)
% 0.39/0.57          | ~ (v1_borsuk_1 @ X14 @ X13)
% 0.39/0.57          | ~ (l1_pre_topc @ X13)
% 0.39/0.57          | ~ (v2_pre_topc @ X13)
% 0.39/0.57          | (v2_struct_0 @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [t87_tsep_1])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_A)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57          | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.39/0.57          | (r4_tsep_1 @ sk_A @ sk_C @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_A)
% 0.39/0.57          | ~ (v1_borsuk_1 @ X0 @ sk_A)
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.39/0.57          | (r4_tsep_1 @ sk_A @ sk_C @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (((r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.39/0.57        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '8'])).
% 0.39/0.57  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('11', plain, (((r4_tsep_1 @ sk_A @ sk_C @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('13', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.39/0.57      inference('clc', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_F @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t145_tmap_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.57             ( l1_pre_topc @ B ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.57               ( ![D:$i]:
% 0.39/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.39/0.57                   ( ( r1_tsep_1 @ C @ D ) =>
% 0.39/0.57                     ( ![E:$i]:
% 0.39/0.57                       ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                           ( v1_funct_2 @
% 0.39/0.57                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.39/0.57                           ( m1_subset_1 @
% 0.39/0.57                             E @ 
% 0.39/0.57                             ( k1_zfmisc_1 @
% 0.39/0.57                               ( k2_zfmisc_1 @
% 0.39/0.57                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                         ( ![F:$i]:
% 0.39/0.57                           ( ( ( v1_funct_1 @ F ) & 
% 0.39/0.57                               ( v1_funct_2 @
% 0.39/0.57                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.39/0.57                               ( m1_subset_1 @
% 0.39/0.57                                 F @ 
% 0.39/0.57                                 ( k1_zfmisc_1 @
% 0.39/0.57                                   ( k2_zfmisc_1 @
% 0.39/0.57                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57                             ( ( r4_tsep_1 @ A @ C @ D ) =>
% 0.39/0.57                               ( ( v1_funct_1 @
% 0.39/0.57                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.39/0.57                                 ( v1_funct_2 @
% 0.39/0.57                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.39/0.57                                   ( u1_struct_0 @ B ) ) & 
% 0.39/0.57                                 ( v5_pre_topc @
% 0.39/0.57                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57                                   ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.39/0.57                                 ( m1_subset_1 @
% 0.39/0.57                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57                                   ( k1_zfmisc_1 @
% 0.39/0.57                                     ( k2_zfmisc_1 @
% 0.39/0.57                                       ( u1_struct_0 @
% 0.39/0.57                                         ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.39/0.57                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X6)
% 0.39/0.57          | ~ (v2_pre_topc @ X6)
% 0.39/0.57          | ~ (l1_pre_topc @ X6)
% 0.39/0.57          | (v2_struct_0 @ X7)
% 0.39/0.57          | ~ (m1_pre_topc @ X7 @ X8)
% 0.39/0.57          | ~ (v1_funct_1 @ X9)
% 0.39/0.57          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 0.39/0.57          | ~ (v5_pre_topc @ X9 @ X7 @ X6)
% 0.39/0.57          | ~ (m1_subset_1 @ X9 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 0.39/0.57          | (v5_pre_topc @ (k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9) @ 
% 0.39/0.57             (k1_tsep_1 @ X8 @ X10 @ X7) @ X6)
% 0.39/0.57          | ~ (r4_tsep_1 @ X8 @ X10 @ X7)
% 0.39/0.57          | ~ (m1_subset_1 @ X11 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))))
% 0.39/0.57          | ~ (v5_pre_topc @ X11 @ X10 @ X6)
% 0.39/0.57          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))
% 0.39/0.57          | ~ (v1_funct_1 @ X11)
% 0.39/0.57          | ~ (r1_tsep_1 @ X10 @ X7)
% 0.39/0.57          | ~ (m1_pre_topc @ X10 @ X8)
% 0.39/0.57          | (v2_struct_0 @ X10)
% 0.39/0.57          | ~ (l1_pre_topc @ X8)
% 0.39/0.57          | ~ (v2_pre_topc @ X8)
% 0.39/0.57          | (v2_struct_0 @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [t145_tmap_1])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.57          | ~ (r1_tsep_1 @ X1 @ sk_D)
% 0.39/0.57          | ~ (v1_funct_1 @ X2)
% 0.39/0.57          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v5_pre_topc @ X2 @ X1 @ sk_B)
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (r4_tsep_1 @ X0 @ X1 @ sk_D)
% 0.39/0.57          | (v5_pre_topc @ (k10_tmap_1 @ X0 @ sk_B @ X1 @ sk_D @ X2 @ sk_F) @ 
% 0.39/0.57             (k1_tsep_1 @ X0 @ X1 @ sk_D) @ sk_B)
% 0.39/0.57          | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ sk_F)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.57  thf('18', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('20', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('22', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v2_struct_0 @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.39/0.57          | ~ (r1_tsep_1 @ X1 @ sk_D)
% 0.39/0.57          | ~ (v1_funct_1 @ X2)
% 0.39/0.57          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v5_pre_topc @ X2 @ X1 @ sk_B)
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (r4_tsep_1 @ X0 @ X1 @ sk_D)
% 0.39/0.57          | (v5_pre_topc @ (k10_tmap_1 @ X0 @ sk_B @ X1 @ sk_D @ X2 @ sk_F) @ 
% 0.39/0.57             (k1_tsep_1 @ X0 @ X1 @ sk_D) @ sk_B)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | (v2_struct_0 @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['17', '18', '19', '20', '21', '22'])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v5_pre_topc @ 
% 0.39/0.57             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.39/0.57          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.39/0.57          | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.57          | ~ (r1_tsep_1 @ sk_C @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['14', '23'])).
% 0.39/0.57  thf('25', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('28', plain, ((r1_tsep_1 @ sk_C @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v2_struct_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v5_pre_topc @ 
% 0.39/0.57             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57             (k1_tsep_1 @ X0 @ sk_C @ sk_D) @ sk_B)
% 0.39/0.57          | ~ (r4_tsep_1 @ X0 @ sk_C @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_A)
% 0.39/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.57        | (v5_pre_topc @ 
% 0.39/0.57           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.39/0.57        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_D)
% 0.39/0.57        | (v2_struct_0 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['13', '29'])).
% 0.39/0.57  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v5_pre_topc @ 
% 0.39/0.57           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_D)
% 0.39/0.57        | (v2_struct_0 @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.39/0.57        | ~ (v1_funct_2 @ 
% 0.39/0.57             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57             (u1_struct_0 @ sk_B))
% 0.39/0.57        | ~ (v5_pre_topc @ 
% 0.39/0.57             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57             (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.39/0.57        | ~ (m1_subset_1 @ 
% 0.39/0.57             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57             (k1_zfmisc_1 @ 
% 0.39/0.57              (k2_zfmisc_1 @ 
% 0.39/0.57               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B)))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      ((~ (v5_pre_topc @ 
% 0.39/0.57           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v5_pre_topc @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.39/0.57      inference('split', [status(esa)], ['36'])).
% 0.39/0.57  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_F @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_k10_tmap_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.57         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.39/0.57         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 0.39/0.57         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.39/0.57         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 0.39/0.57         ( v1_funct_1 @ E ) & 
% 0.39/0.57         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           E @ 
% 0.39/0.57           ( k1_zfmisc_1 @
% 0.39/0.57             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.39/0.57         ( v1_funct_1 @ F ) & 
% 0.39/0.57         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           F @ 
% 0.39/0.57           ( k1_zfmisc_1 @
% 0.39/0.57             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.57       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.39/0.57         ( v1_funct_2 @
% 0.39/0.57           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.57           ( k1_zfmisc_1 @
% 0.39/0.57             ( k2_zfmisc_1 @
% 0.39/0.57               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.39/0.57               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ 
% 0.39/0.57             (k1_zfmisc_1 @ 
% 0.39/0.57              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.39/0.57          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X3 @ X4)
% 0.39/0.57          | (v2_struct_0 @ X3)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ X4)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (l1_pre_topc @ X2)
% 0.39/0.57          | ~ (v2_pre_topc @ X2)
% 0.39/0.57          | (v2_struct_0 @ X2)
% 0.39/0.57          | ~ (l1_pre_topc @ X4)
% 0.39/0.57          | ~ (v2_pre_topc @ X4)
% 0.39/0.57          | (v2_struct_0 @ X4)
% 0.39/0.57          | ~ (v1_funct_1 @ X5)
% 0.39/0.57          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.39/0.57          | ~ (m1_subset_1 @ X5 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.39/0.57          | (m1_subset_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.39/0.57             (k1_zfmisc_1 @ 
% 0.39/0.57              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ 
% 0.39/0.57               (u1_struct_0 @ X2)))))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.39/0.57           (k1_zfmisc_1 @ 
% 0.39/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.39/0.57             (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ X2)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (v2_pre_topc @ X1)
% 0.39/0.57          | ~ (l1_pre_topc @ X1)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.57  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('45', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('47', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.39/0.57           (k1_zfmisc_1 @ 
% 0.39/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.39/0.57             (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ X2)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (v2_pre_topc @ X1)
% 0.39/0.57          | ~ (l1_pre_topc @ X1)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_F)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | (m1_subset_1 @ 
% 0.39/0.57             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57             (k1_zfmisc_1 @ 
% 0.39/0.57              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['39', '47'])).
% 0.39/0.57  thf('49', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('51', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | (m1_subset_1 @ 
% 0.39/0.57             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57             (k1_zfmisc_1 @ 
% 0.39/0.57              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B)))))),
% 0.39/0.57      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      (((m1_subset_1 @ 
% 0.39/0.57         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (k1_zfmisc_1 @ 
% 0.39/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57           (u1_struct_0 @ sk_B))))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['38', '51'])).
% 0.39/0.57  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('56', plain,
% 0.39/0.57      (((m1_subset_1 @ 
% 0.39/0.57         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (k1_zfmisc_1 @ 
% 0.39/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57           (u1_struct_0 @ sk_B))))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_D))),
% 0.39/0.57      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.39/0.57  thf('57', plain,
% 0.39/0.57      ((~ (m1_subset_1 @ 
% 0.39/0.57           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57           (k1_zfmisc_1 @ 
% 0.39/0.57            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57             (u1_struct_0 @ sk_B)))))
% 0.39/0.57         <= (~
% 0.39/0.57             ((m1_subset_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ 
% 0.39/0.57                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57                 (u1_struct_0 @ sk_B))))))),
% 0.39/0.57      inference('split', [status(esa)], ['36'])).
% 0.39/0.57  thf('58', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_D)
% 0.39/0.57         | (v2_struct_0 @ sk_C)
% 0.39/0.57         | (v2_struct_0 @ sk_B)
% 0.39/0.57         | (v2_struct_0 @ sk_A)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((m1_subset_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ 
% 0.39/0.57                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57                 (u1_struct_0 @ sk_B))))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.39/0.57  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('60', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((m1_subset_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ 
% 0.39/0.57                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57                 (u1_struct_0 @ sk_B))))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.57  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('62', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((m1_subset_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ 
% 0.39/0.57                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57                 (u1_struct_0 @ sk_B))))))),
% 0.39/0.57      inference('clc', [status(thm)], ['60', '61'])).
% 0.39/0.57  thf('63', plain, (~ (v2_struct_0 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('64', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_C))
% 0.39/0.57         <= (~
% 0.39/0.57             ((m1_subset_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ 
% 0.39/0.57                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57                 (u1_struct_0 @ sk_B))))))),
% 0.39/0.57      inference('clc', [status(thm)], ['62', '63'])).
% 0.39/0.57  thf('65', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('66', plain,
% 0.39/0.57      (((m1_subset_1 @ 
% 0.39/0.57         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (k1_zfmisc_1 @ 
% 0.39/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57           (u1_struct_0 @ sk_B)))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['64', '65'])).
% 0.39/0.57  thf('67', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('68', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_F @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('69', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('70', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ 
% 0.39/0.57             (k1_zfmisc_1 @ 
% 0.39/0.57              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.39/0.57          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X3 @ X4)
% 0.39/0.57          | (v2_struct_0 @ X3)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ X4)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (l1_pre_topc @ X2)
% 0.39/0.57          | ~ (v2_pre_topc @ X2)
% 0.39/0.57          | (v2_struct_0 @ X2)
% 0.39/0.57          | ~ (l1_pre_topc @ X4)
% 0.39/0.57          | ~ (v2_pre_topc @ X4)
% 0.39/0.57          | (v2_struct_0 @ X4)
% 0.39/0.57          | ~ (v1_funct_1 @ X5)
% 0.39/0.57          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.39/0.57          | ~ (m1_subset_1 @ X5 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.39/0.57          | (v1_funct_2 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.39/0.57             (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ (u1_struct_0 @ X2)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.39/0.57  thf('71', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.39/0.57           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ X2)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (v2_pre_topc @ X1)
% 0.39/0.57          | ~ (l1_pre_topc @ X1)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.39/0.57  thf('72', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('74', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('75', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('76', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.39/0.57           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ X2)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (v2_pre_topc @ X1)
% 0.39/0.57          | ~ (l1_pre_topc @ X1)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 0.39/0.57  thf('77', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_F)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | (v1_funct_2 @ 
% 0.39/0.57             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.39/0.57             (u1_struct_0 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['68', '76'])).
% 0.39/0.57  thf('78', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('79', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('80', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | (v1_funct_2 @ 
% 0.39/0.57             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.39/0.57             (u1_struct_0 @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.39/0.57  thf('81', plain,
% 0.39/0.57      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57         (u1_struct_0 @ sk_B))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['67', '80'])).
% 0.39/0.57  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('84', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('85', plain,
% 0.39/0.57      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57         (u1_struct_0 @ sk_B))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_D))),
% 0.39/0.57      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 0.39/0.57  thf('86', plain,
% 0.39/0.57      ((~ (v1_funct_2 @ 
% 0.39/0.57           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57           (u1_struct_0 @ sk_B)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_2 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('split', [status(esa)], ['36'])).
% 0.39/0.57  thf('87', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_D)
% 0.39/0.57         | (v2_struct_0 @ sk_C)
% 0.39/0.57         | (v2_struct_0 @ sk_B)
% 0.39/0.57         | (v2_struct_0 @ sk_A)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_2 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.57  thf('88', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('89', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_2 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['87', '88'])).
% 0.39/0.57  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('91', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_2 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('clc', [status(thm)], ['89', '90'])).
% 0.39/0.57  thf('92', plain, (~ (v2_struct_0 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('93', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_C))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_2 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57               (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('clc', [status(thm)], ['91', '92'])).
% 0.39/0.57  thf('94', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('95', plain,
% 0.39/0.57      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57         (u1_struct_0 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['93', '94'])).
% 0.39/0.57  thf('96', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('97', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_F @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('98', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ 
% 0.39/0.57        (k1_zfmisc_1 @ 
% 0.39/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('99', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ 
% 0.39/0.57             (k1_zfmisc_1 @ 
% 0.39/0.57              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.39/0.57          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | ~ (m1_pre_topc @ X3 @ X4)
% 0.39/0.57          | (v2_struct_0 @ X3)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ X4)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (l1_pre_topc @ X2)
% 0.39/0.57          | ~ (v2_pre_topc @ X2)
% 0.39/0.57          | (v2_struct_0 @ X2)
% 0.39/0.57          | ~ (l1_pre_topc @ X4)
% 0.39/0.57          | ~ (v2_pre_topc @ X4)
% 0.39/0.57          | (v2_struct_0 @ X4)
% 0.39/0.57          | ~ (v1_funct_1 @ X5)
% 0.39/0.57          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.39/0.57          | ~ (m1_subset_1 @ X5 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.39/0.57          | (v1_funct_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.39/0.57  thf('100', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | (v2_struct_0 @ X2)
% 0.39/0.57          | ~ (v2_pre_topc @ X2)
% 0.39/0.57          | ~ (l1_pre_topc @ X2)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ X2)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['98', '99'])).
% 0.39/0.57  thf('101', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('103', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('104', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('105', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ 
% 0.39/0.57               (k1_zfmisc_1 @ 
% 0.39/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.39/0.57          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | (v2_struct_0 @ X2)
% 0.39/0.57          | ~ (v2_pre_topc @ X2)
% 0.39/0.57          | ~ (l1_pre_topc @ X2)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.39/0.57          | (v2_struct_0 @ X1)
% 0.39/0.57          | ~ (m1_pre_topc @ X1 @ X2))),
% 0.39/0.57      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 0.39/0.57  thf('106', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_F)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.39/0.57          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['97', '105'])).
% 0.39/0.57  thf('107', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('108', plain,
% 0.39/0.57      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('109', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_pre_topc @ sk_D @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_D)
% 0.39/0.57          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.57          | (v2_struct_0 @ sk_C)
% 0.39/0.57          | (v2_struct_0 @ sk_B)
% 0.39/0.57          | ~ (l1_pre_topc @ X0)
% 0.39/0.57          | ~ (v2_pre_topc @ X0)
% 0.39/0.57          | (v2_struct_0 @ X0)
% 0.39/0.57          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.39/0.57      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.39/0.57  thf('110', plain,
% 0.39/0.57      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['96', '109'])).
% 0.39/0.57  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('113', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('114', plain,
% 0.39/0.57      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.39/0.57        | (v2_struct_0 @ sk_A)
% 0.39/0.57        | (v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_D))),
% 0.39/0.57      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.39/0.57  thf('115', plain,
% 0.39/0.57      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.39/0.57      inference('split', [status(esa)], ['36'])).
% 0.39/0.57  thf('116', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_D)
% 0.39/0.57         | (v2_struct_0 @ sk_C)
% 0.39/0.57         | (v2_struct_0 @ sk_B)
% 0.39/0.57         | (v2_struct_0 @ sk_A)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['114', '115'])).
% 0.39/0.57  thf('117', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('118', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['116', '117'])).
% 0.39/0.57  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('120', plain,
% 0.39/0.57      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.39/0.57      inference('clc', [status(thm)], ['118', '119'])).
% 0.39/0.57  thf('121', plain, (~ (v2_struct_0 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('122', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_C))
% 0.39/0.57         <= (~
% 0.39/0.57             ((v1_funct_1 @ 
% 0.39/0.57               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.39/0.57      inference('clc', [status(thm)], ['120', '121'])).
% 0.39/0.57  thf('123', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('124', plain,
% 0.39/0.57      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['122', '123'])).
% 0.39/0.57  thf('125', plain,
% 0.39/0.57      (~
% 0.39/0.57       ((v5_pre_topc @ 
% 0.39/0.57         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) | 
% 0.39/0.57       ~
% 0.39/0.57       ((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))) | 
% 0.39/0.57       ~
% 0.39/0.57       ((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57         (u1_struct_0 @ sk_B))) | 
% 0.39/0.57       ~
% 0.39/0.57       ((m1_subset_1 @ 
% 0.39/0.57         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (k1_zfmisc_1 @ 
% 0.39/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.39/0.57           (u1_struct_0 @ sk_B)))))),
% 0.39/0.57      inference('split', [status(esa)], ['36'])).
% 0.39/0.57  thf('126', plain,
% 0.39/0.57      (~
% 0.39/0.57       ((v5_pre_topc @ 
% 0.39/0.57         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57         (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.39/0.57      inference('sat_resolution*', [status(thm)], ['66', '95', '124', '125'])).
% 0.39/0.57  thf('127', plain,
% 0.39/0.57      (~ (v5_pre_topc @ 
% 0.39/0.57          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.57          (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)),
% 0.39/0.57      inference('simpl_trail', [status(thm)], ['37', '126'])).
% 0.39/0.57  thf('128', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_B)
% 0.39/0.57        | (v2_struct_0 @ sk_D)
% 0.39/0.57        | (v2_struct_0 @ sk_C)
% 0.39/0.57        | (v2_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['35', '127'])).
% 0.39/0.57  thf('129', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('130', plain,
% 0.39/0.57      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['128', '129'])).
% 0.39/0.57  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('132', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.39/0.57      inference('clc', [status(thm)], ['130', '131'])).
% 0.39/0.57  thf('133', plain, (~ (v2_struct_0 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('134', plain, ((v2_struct_0 @ sk_C)),
% 0.39/0.57      inference('clc', [status(thm)], ['132', '133'])).
% 0.39/0.57  thf('135', plain, ($false), inference('demod', [status(thm)], ['0', '134'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
