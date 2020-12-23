%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SH1FpBJkEB

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:12 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 328 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   21
%              Number of atoms          : 2534 (26634 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   32 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

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

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t147_tmap_1,conjecture,(
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
                           => ( ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ ( k3_tmap_1 @ A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) )
                             => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                                & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                                & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                             => ( ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ ( k3_tmap_1 @ A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) )
                               => ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                  & ( v1_funct_2 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                                  & ( v5_pre_topc @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                                  & ( m1_subset_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_E ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('2',plain,(
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
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ ( k2_tsep_1 @ X8 @ X10 @ X7 ) ) @ ( u1_struct_0 @ X6 ) @ ( k3_tmap_1 @ X8 @ X6 @ X10 @ ( k2_tsep_1 @ X8 @ X10 @ X7 ) @ X11 ) @ ( k3_tmap_1 @ X8 @ X6 @ X7 @ ( k2_tsep_1 @ X8 @ X10 @ X7 ) @ X9 ) )
      | ~ ( r4_tsep_1 @ X8 @ X10 @ X7 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v5_pre_topc @ X11 @ X10 @ X6 )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ( r1_tsep_1 @ X10 @ X7 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t144_tmap_1])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
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
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( r4_tsep_1 @ X13 @ X12 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( v1_tsep_1 @ X14 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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

thf('24',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v5_pre_topc @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6','7','8','9','10','23','24','25','26','27','28','29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
   <= ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
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

thf('37',plain,(
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

thf('38',plain,(
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
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
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
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,(
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
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','47'])).

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
    ( ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['32'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
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

thf('67',plain,(
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
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
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
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
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
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
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

thf('96',plain,(
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
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
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
    inference(demod,[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
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
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
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
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['92','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['32'])).

thf('112',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(split,[status(esa)],['32'])).

thf('122',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['62','91','120','121'])).

thf('123',plain,(
    ~ ( v5_pre_topc @ ( k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_tsep_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['33','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','123'])).

thf('125',plain,(
    ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['0','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SH1FpBJkEB
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 91 iterations in 0.110s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.58  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.38/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.58  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.38/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.38/0.58  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.38/0.58  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.38/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.38/0.58  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(k10_tmap_1_type, type, k10_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.58  thf(t147_tmap_1, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_tsep_1 @ C @ A ) & 
% 0.38/0.58                 ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.38/0.58                     ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.58                   ( ( ~( r1_tsep_1 @ C @ D ) ) =>
% 0.38/0.58                     ( ![E:$i]:
% 0.38/0.58                       ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.58                           ( v1_funct_2 @
% 0.38/0.58                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.38/0.58                           ( m1_subset_1 @
% 0.38/0.58                             E @ 
% 0.38/0.58                             ( k1_zfmisc_1 @
% 0.38/0.58                               ( k2_zfmisc_1 @
% 0.38/0.58                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                         ( ![F:$i]:
% 0.38/0.58                           ( ( ( v1_funct_1 @ F ) & 
% 0.38/0.58                               ( v1_funct_2 @
% 0.38/0.58                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.38/0.58                               ( m1_subset_1 @
% 0.38/0.58                                 F @ 
% 0.38/0.58                                 ( k1_zfmisc_1 @
% 0.38/0.58                                   ( k2_zfmisc_1 @
% 0.38/0.58                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                             ( ( r2_funct_2 @
% 0.38/0.58                                 ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58                                 ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                 ( k3_tmap_1 @
% 0.38/0.58                                   A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ 
% 0.38/0.58                                 ( k3_tmap_1 @
% 0.38/0.58                                   A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) =>
% 0.38/0.58                               ( ( v1_funct_1 @
% 0.38/0.58                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.38/0.58                                 ( v1_funct_2 @
% 0.38/0.58                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58                                   ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                                 ( v5_pre_topc @
% 0.38/0.58                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58                                   ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.38/0.58                                 ( m1_subset_1 @
% 0.38/0.58                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58                                   ( k1_zfmisc_1 @
% 0.38/0.58                                     ( k2_zfmisc_1 @
% 0.38/0.58                                       ( u1_struct_0 @
% 0.38/0.58                                         ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.58            ( l1_pre_topc @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58                ( l1_pre_topc @ B ) ) =>
% 0.38/0.58              ( ![C:$i]:
% 0.38/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_tsep_1 @ C @ A ) & 
% 0.38/0.58                    ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.58                  ( ![D:$i]:
% 0.38/0.58                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ A ) & 
% 0.38/0.58                        ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.58                      ( ( ~( r1_tsep_1 @ C @ D ) ) =>
% 0.38/0.58                        ( ![E:$i]:
% 0.38/0.58                          ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.58                              ( v1_funct_2 @
% 0.38/0.58                                E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                              ( v5_pre_topc @ E @ C @ B ) & 
% 0.38/0.58                              ( m1_subset_1 @
% 0.38/0.58                                E @ 
% 0.38/0.58                                ( k1_zfmisc_1 @
% 0.38/0.58                                  ( k2_zfmisc_1 @
% 0.38/0.58                                    ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                            ( ![F:$i]:
% 0.38/0.58                              ( ( ( v1_funct_1 @ F ) & 
% 0.38/0.58                                  ( v1_funct_2 @
% 0.38/0.58                                    F @ ( u1_struct_0 @ D ) @ 
% 0.38/0.58                                    ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                                  ( v5_pre_topc @ F @ D @ B ) & 
% 0.38/0.58                                  ( m1_subset_1 @
% 0.38/0.58                                    F @ 
% 0.38/0.58                                    ( k1_zfmisc_1 @
% 0.38/0.58                                      ( k2_zfmisc_1 @
% 0.38/0.58                                        ( u1_struct_0 @ D ) @ 
% 0.38/0.58                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                                ( ( r2_funct_2 @
% 0.38/0.58                                    ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58                                    ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                    ( k3_tmap_1 @
% 0.38/0.58                                      A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ 
% 0.38/0.58                                    ( k3_tmap_1 @
% 0.38/0.58                                      A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) =>
% 0.38/0.58                                  ( ( v1_funct_1 @
% 0.38/0.58                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.38/0.58                                    ( v1_funct_2 @
% 0.38/0.58                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58                                      ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58                                      ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                                    ( v5_pre_topc @
% 0.38/0.58                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58                                      ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.38/0.58                                    ( m1_subset_1 @
% 0.38/0.58                                      ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58                                      ( k1_zfmisc_1 @
% 0.38/0.58                                        ( k2_zfmisc_1 @
% 0.38/0.58                                          ( u1_struct_0 @
% 0.38/0.58                                            ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58                                          ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t147_tmap_1])).
% 0.38/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      ((r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58        (u1_struct_0 @ sk_B) @ 
% 0.38/0.58        (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.58         sk_E) @ 
% 0.38/0.58        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ (k2_tsep_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.38/0.58         sk_F))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t144_tmap_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.58                   ( ( ~( r1_tsep_1 @ C @ D ) ) =>
% 0.38/0.58                     ( ![E:$i]:
% 0.38/0.58                       ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.58                           ( v1_funct_2 @
% 0.38/0.58                             E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                           ( v5_pre_topc @ E @ C @ B ) & 
% 0.38/0.58                           ( m1_subset_1 @
% 0.38/0.58                             E @ 
% 0.38/0.58                             ( k1_zfmisc_1 @
% 0.38/0.58                               ( k2_zfmisc_1 @
% 0.38/0.58                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                         ( ![F:$i]:
% 0.38/0.58                           ( ( ( v1_funct_1 @ F ) & 
% 0.38/0.58                               ( v1_funct_2 @
% 0.38/0.58                                 F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                               ( v5_pre_topc @ F @ D @ B ) & 
% 0.38/0.58                               ( m1_subset_1 @
% 0.38/0.58                                 F @ 
% 0.38/0.58                                 ( k1_zfmisc_1 @
% 0.38/0.58                                   ( k2_zfmisc_1 @
% 0.38/0.58                                     ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                             ( ( ( r2_funct_2 @
% 0.38/0.58                                   ( u1_struct_0 @ ( k2_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58                                   ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                   ( k3_tmap_1 @
% 0.38/0.58                                     A @ B @ C @ ( k2_tsep_1 @ A @ C @ D ) @ E ) @ 
% 0.38/0.58                                   ( k3_tmap_1 @
% 0.38/0.58                                     A @ B @ D @ ( k2_tsep_1 @ A @ C @ D ) @ F ) ) & 
% 0.38/0.58                                 ( r4_tsep_1 @ A @ C @ D ) ) =>
% 0.38/0.58                               ( ( v1_funct_1 @
% 0.38/0.58                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.38/0.58                                 ( v1_funct_2 @
% 0.38/0.58                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58                                   ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                                 ( v5_pre_topc @
% 0.38/0.58                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58                                   ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.38/0.58                                 ( m1_subset_1 @
% 0.38/0.58                                   ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58                                   ( k1_zfmisc_1 @
% 0.38/0.58                                     ( k2_zfmisc_1 @
% 0.38/0.58                                       ( u1_struct_0 @
% 0.38/0.58                                         ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58                                       ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X6)
% 0.38/0.58          | ~ (v2_pre_topc @ X6)
% 0.38/0.58          | ~ (l1_pre_topc @ X6)
% 0.38/0.58          | (v2_struct_0 @ X7)
% 0.38/0.58          | ~ (m1_pre_topc @ X7 @ X8)
% 0.38/0.58          | ~ (v1_funct_1 @ X9)
% 0.38/0.58          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 0.38/0.58          | ~ (v5_pre_topc @ X9 @ X7 @ X6)
% 0.38/0.58          | ~ (m1_subset_1 @ X9 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 0.38/0.58          | (v5_pre_topc @ (k10_tmap_1 @ X8 @ X6 @ X10 @ X7 @ X11 @ X9) @ 
% 0.38/0.58             (k1_tsep_1 @ X8 @ X10 @ X7) @ X6)
% 0.38/0.58          | ~ (r2_funct_2 @ (u1_struct_0 @ (k2_tsep_1 @ X8 @ X10 @ X7)) @ 
% 0.38/0.58               (u1_struct_0 @ X6) @ 
% 0.38/0.58               (k3_tmap_1 @ X8 @ X6 @ X10 @ (k2_tsep_1 @ X8 @ X10 @ X7) @ X11) @ 
% 0.38/0.58               (k3_tmap_1 @ X8 @ X6 @ X7 @ (k2_tsep_1 @ X8 @ X10 @ X7) @ X9))
% 0.38/0.58          | ~ (r4_tsep_1 @ X8 @ X10 @ X7)
% 0.38/0.58          | ~ (m1_subset_1 @ X11 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))))
% 0.38/0.58          | ~ (v5_pre_topc @ X11 @ X10 @ X6)
% 0.38/0.58          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X6))
% 0.38/0.58          | ~ (v1_funct_1 @ X11)
% 0.38/0.58          | (r1_tsep_1 @ X10 @ X7)
% 0.38/0.58          | ~ (m1_pre_topc @ X10 @ X8)
% 0.38/0.58          | (v2_struct_0 @ X10)
% 0.38/0.58          | ~ (l1_pre_topc @ X8)
% 0.38/0.58          | ~ (v2_pre_topc @ X8)
% 0.38/0.58          | (v2_struct_0 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [t144_tmap_1])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.58        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.38/0.58        | ~ (v1_funct_1 @ sk_E)
% 0.38/0.58        | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B)
% 0.38/0.58        | ~ (m1_subset_1 @ sk_E @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58        | ~ (r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.58        | (v5_pre_topc @ 
% 0.38/0.58           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.38/0.58        | ~ (m1_subset_1 @ sk_F @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58        | ~ (v5_pre_topc @ sk_F @ sk_D @ sk_B)
% 0.38/0.58        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | ~ (v1_funct_1 @ sk_F)
% 0.38/0.58        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_D)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('9', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_E @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('11', plain, ((v1_tsep_1 @ sk_D @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('12', plain, ((v1_tsep_1 @ sk_C @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t88_tsep_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.58               ( r4_tsep_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.58         (~ (v1_tsep_1 @ X12 @ X13)
% 0.38/0.58          | ~ (m1_pre_topc @ X12 @ X13)
% 0.38/0.58          | (r4_tsep_1 @ X13 @ X12 @ X14)
% 0.38/0.58          | ~ (m1_pre_topc @ X14 @ X13)
% 0.38/0.58          | ~ (v1_tsep_1 @ X14 @ X13)
% 0.38/0.58          | ~ (l1_pre_topc @ X13)
% 0.38/0.58          | ~ (v2_pre_topc @ X13)
% 0.38/0.58          | (v2_struct_0 @ X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [t88_tsep_1])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_A)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.58          | (r4_tsep_1 @ sk_A @ sk_C @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_A)
% 0.38/0.58          | ~ (v1_tsep_1 @ X0 @ sk_A)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.58          | (r4_tsep_1 @ sk_A @ sk_C @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (((r4_tsep_1 @ sk_A @ sk_C @ sk_D)
% 0.38/0.58        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['11', '18'])).
% 0.38/0.58  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('21', plain, (((r4_tsep_1 @ sk_A @ sk_C @ sk_D) | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.58  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('23', plain, ((r4_tsep_1 @ sk_A @ sk_C @ sk_D)),
% 0.38/0.58      inference('clc', [status(thm)], ['21', '22'])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_F @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('25', plain, ((v5_pre_topc @ sk_F @ sk_D @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('27', plain, ((v1_funct_1 @ sk_F)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('30', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.38/0.58        | (v5_pre_topc @ 
% 0.38/0.58           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)],
% 0.38/0.58                ['3', '4', '5', '6', '7', '8', '9', '10', '23', '24', '25', 
% 0.38/0.58                 '26', '27', '28', '29', '30'])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.38/0.58        | ~ (v1_funct_2 @ 
% 0.38/0.58             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58             (u1_struct_0 @ sk_B))
% 0.38/0.58        | ~ (v5_pre_topc @ 
% 0.38/0.58             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58             (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.38/0.58        | ~ (m1_subset_1 @ 
% 0.38/0.58             (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ 
% 0.38/0.58               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B)))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      ((~ (v5_pre_topc @ 
% 0.38/0.58           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58           (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v5_pre_topc @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))),
% 0.38/0.58      inference('split', [status(esa)], ['32'])).
% 0.38/0.58  thf('34', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_F @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_E @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(dt_k10_tmap_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.58         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.38/0.58         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & 
% 0.38/0.58         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.38/0.58         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) & 
% 0.38/0.58         ( v1_funct_1 @ E ) & 
% 0.38/0.58         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @
% 0.38/0.58           E @ 
% 0.38/0.58           ( k1_zfmisc_1 @
% 0.38/0.58             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.38/0.58         ( v1_funct_1 @ F ) & 
% 0.38/0.58         ( v1_funct_2 @ F @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @
% 0.38/0.58           F @ 
% 0.38/0.58           ( k1_zfmisc_1 @
% 0.38/0.58             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58       ( ( v1_funct_1 @ ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.38/0.58         ( v1_funct_2 @
% 0.38/0.58           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58           ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58         ( m1_subset_1 @
% 0.38/0.58           ( k10_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.58           ( k1_zfmisc_1 @
% 0.38/0.58             ( k2_zfmisc_1 @
% 0.38/0.58               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.38/0.58               ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X0 @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.38/0.58          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X3 @ X4)
% 0.38/0.58          | (v2_struct_0 @ X3)
% 0.38/0.58          | ~ (m1_pre_topc @ X1 @ X4)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X2)
% 0.38/0.58          | ~ (v2_pre_topc @ X2)
% 0.38/0.58          | (v2_struct_0 @ X2)
% 0.38/0.58          | ~ (l1_pre_topc @ X4)
% 0.38/0.58          | ~ (v2_pre_topc @ X4)
% 0.38/0.58          | (v2_struct_0 @ X4)
% 0.38/0.58          | ~ (v1_funct_1 @ X5)
% 0.38/0.58          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.38/0.58          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.38/0.58          | (v1_funct_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | (v2_struct_0 @ X2)
% 0.38/0.58          | ~ (v2_pre_topc @ X2)
% 0.38/0.58          | ~ (l1_pre_topc @ X2)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (m1_pre_topc @ X1 @ X2)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.58          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v1_funct_1 @ (k10_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | (v2_struct_0 @ X2)
% 0.38/0.58          | ~ (v2_pre_topc @ X2)
% 0.38/0.58          | ~ (l1_pre_topc @ X2)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X2)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (m1_pre_topc @ X1 @ X2))),
% 0.38/0.58      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_D)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_F)
% 0.38/0.58          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['35', '43'])).
% 0.38/0.58  thf('45', plain, ((v1_funct_1 @ sk_F)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_D)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | (v1_funct_1 @ (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['34', '47'])).
% 0.38/0.58  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('51', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | (v2_struct_0 @ sk_D))),
% 0.38/0.58      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      ((~ (v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.58      inference('split', [status(esa)], ['32'])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_D)
% 0.38/0.58         | (v2_struct_0 @ sk_C)
% 0.38/0.58         | (v2_struct_0 @ sk_B)
% 0.38/0.58         | (v2_struct_0 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.58  thf('55', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.58  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.58      inference('clc', [status(thm)], ['56', '57'])).
% 0.38/0.58  thf('59', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_C))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))))),
% 0.38/0.58      inference('clc', [status(thm)], ['58', '59'])).
% 0.38/0.58  thf('61', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      (((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.58  thf('63', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_F @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_E @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('66', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X0 @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.38/0.58          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X3 @ X4)
% 0.38/0.58          | (v2_struct_0 @ X3)
% 0.38/0.58          | ~ (m1_pre_topc @ X1 @ X4)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X2)
% 0.38/0.58          | ~ (v2_pre_topc @ X2)
% 0.38/0.58          | (v2_struct_0 @ X2)
% 0.38/0.58          | ~ (l1_pre_topc @ X4)
% 0.38/0.58          | ~ (v2_pre_topc @ X4)
% 0.38/0.58          | (v2_struct_0 @ X4)
% 0.38/0.58          | ~ (v1_funct_1 @ X5)
% 0.38/0.58          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.38/0.58          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.38/0.58          | (v1_funct_2 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.38/0.58             (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ (u1_struct_0 @ X2)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.38/0.58           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_1 @ X2)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (v2_pre_topc @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X1)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.58          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.38/0.58  thf('68', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('72', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v1_funct_2 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.38/0.58           (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_1 @ X2)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (v2_pre_topc @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X1)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.38/0.58      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_D)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_F)
% 0.38/0.58          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | (v1_funct_2 @ 
% 0.38/0.58             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.38/0.58             (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['64', '72'])).
% 0.38/0.58  thf('74', plain, ((v1_funct_1 @ sk_F)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('75', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('76', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_D)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | (v1_funct_2 @ 
% 0.38/0.58             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58             (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.38/0.58             (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.38/0.58  thf('77', plain,
% 0.38/0.58      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58         (u1_struct_0 @ sk_B))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['63', '76'])).
% 0.38/0.58  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('80', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('81', plain,
% 0.38/0.58      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58         (u1_struct_0 @ sk_B))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | (v2_struct_0 @ sk_D))),
% 0.38/0.58      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.38/0.58  thf('82', plain,
% 0.38/0.58      ((~ (v1_funct_2 @ 
% 0.38/0.58           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58           (u1_struct_0 @ sk_B)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_2 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('split', [status(esa)], ['32'])).
% 0.38/0.58  thf('83', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_D)
% 0.38/0.58         | (v2_struct_0 @ sk_C)
% 0.38/0.58         | (v2_struct_0 @ sk_B)
% 0.38/0.58         | (v2_struct_0 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_2 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['81', '82'])).
% 0.38/0.58  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('85', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_2 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.58  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('87', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_2 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('clc', [status(thm)], ['85', '86'])).
% 0.38/0.58  thf('88', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('89', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_C))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_funct_2 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('clc', [status(thm)], ['87', '88'])).
% 0.38/0.58  thf('90', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('91', plain,
% 0.38/0.58      (((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58         (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['89', '90'])).
% 0.38/0.58  thf('92', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('93', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_F @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('94', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_E @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('95', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X0 @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))))
% 0.38/0.58          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ X2))
% 0.38/0.58          | ~ (v1_funct_1 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X3 @ X4)
% 0.38/0.58          | (v2_struct_0 @ X3)
% 0.38/0.58          | ~ (m1_pre_topc @ X1 @ X4)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X2)
% 0.38/0.58          | ~ (v2_pre_topc @ X2)
% 0.38/0.58          | (v2_struct_0 @ X2)
% 0.38/0.58          | ~ (l1_pre_topc @ X4)
% 0.38/0.58          | ~ (v2_pre_topc @ X4)
% 0.38/0.58          | (v2_struct_0 @ X4)
% 0.38/0.58          | ~ (v1_funct_1 @ X5)
% 0.38/0.58          | ~ (v1_funct_2 @ X5 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))
% 0.38/0.58          | ~ (m1_subset_1 @ X5 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X2))))
% 0.38/0.58          | (m1_subset_1 @ (k10_tmap_1 @ X4 @ X2 @ X1 @ X3 @ X0 @ X5) @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X4 @ X1 @ X3)) @ 
% 0.38/0.58               (u1_struct_0 @ X2)))))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k10_tmap_1])).
% 0.38/0.58  thf('96', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.38/0.58           (k1_zfmisc_1 @ 
% 0.38/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.38/0.58             (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_1 @ X2)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (v2_pre_topc @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X1)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.58          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['94', '95'])).
% 0.38/0.58  thf('97', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('98', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('99', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('100', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('101', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((m1_subset_1 @ (k10_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.38/0.58           (k1_zfmisc_1 @ 
% 0.38/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X1 @ sk_C @ X0)) @ 
% 0.38/0.58             (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_1 @ X2)
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (v2_pre_topc @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X1)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.38/0.58      inference('demod', [status(thm)], ['96', '97', '98', '99', '100'])).
% 0.38/0.58  thf('102', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_D)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_F)
% 0.38/0.58          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | (m1_subset_1 @ 
% 0.38/0.58             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B)))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['93', '101'])).
% 0.38/0.58  thf('103', plain, ((v1_funct_1 @ sk_F)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('104', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('105', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ sk_D @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_D)
% 0.38/0.58          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_C)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | (v2_struct_0 @ X0)
% 0.38/0.58          | (m1_subset_1 @ 
% 0.38/0.58             (k10_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X0 @ sk_C @ sk_D)) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B)))))),
% 0.38/0.58      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.38/0.58  thf('106', plain,
% 0.38/0.58      (((m1_subset_1 @ 
% 0.38/0.58         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (k1_zfmisc_1 @ 
% 0.38/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58           (u1_struct_0 @ sk_B))))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_D))),
% 0.38/0.58      inference('sup-', [status(thm)], ['92', '105'])).
% 0.38/0.58  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('109', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('110', plain,
% 0.38/0.58      (((m1_subset_1 @ 
% 0.38/0.58         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (k1_zfmisc_1 @ 
% 0.38/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58           (u1_struct_0 @ sk_B))))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | (v2_struct_0 @ sk_D))),
% 0.38/0.58      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.38/0.58  thf('111', plain,
% 0.38/0.58      ((~ (m1_subset_1 @ 
% 0.38/0.58           (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58           (k1_zfmisc_1 @ 
% 0.38/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58             (u1_struct_0 @ sk_B)))))
% 0.38/0.58         <= (~
% 0.38/0.58             ((m1_subset_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ 
% 0.38/0.58                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58                 (u1_struct_0 @ sk_B))))))),
% 0.38/0.58      inference('split', [status(esa)], ['32'])).
% 0.38/0.58  thf('112', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_D)
% 0.38/0.58         | (v2_struct_0 @ sk_C)
% 0.38/0.58         | (v2_struct_0 @ sk_B)
% 0.38/0.58         | (v2_struct_0 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((m1_subset_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ 
% 0.38/0.58                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58                 (u1_struct_0 @ sk_B))))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['110', '111'])).
% 0.38/0.58  thf('113', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('114', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((m1_subset_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ 
% 0.38/0.58                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58                 (u1_struct_0 @ sk_B))))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['112', '113'])).
% 0.38/0.58  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('116', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((m1_subset_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ 
% 0.38/0.58                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58                 (u1_struct_0 @ sk_B))))))),
% 0.38/0.58      inference('clc', [status(thm)], ['114', '115'])).
% 0.38/0.58  thf('117', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('118', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_C))
% 0.38/0.58         <= (~
% 0.38/0.58             ((m1_subset_1 @ 
% 0.38/0.58               (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ 
% 0.38/0.58                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58                 (u1_struct_0 @ sk_B))))))),
% 0.38/0.58      inference('clc', [status(thm)], ['116', '117'])).
% 0.38/0.58  thf('119', plain, (~ (v2_struct_0 @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('120', plain,
% 0.38/0.58      (((m1_subset_1 @ 
% 0.38/0.58         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (k1_zfmisc_1 @ 
% 0.38/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58           (u1_struct_0 @ sk_B)))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['118', '119'])).
% 0.38/0.58  thf('121', plain,
% 0.38/0.58      (~
% 0.38/0.58       ((v5_pre_topc @ 
% 0.38/0.58         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)) | 
% 0.38/0.58       ~
% 0.38/0.58       ((m1_subset_1 @ 
% 0.38/0.58         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (k1_zfmisc_1 @ 
% 0.38/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58           (u1_struct_0 @ sk_B))))) | 
% 0.38/0.58       ~
% 0.38/0.58       ((v1_funct_2 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_C @ sk_D)) @ 
% 0.38/0.58         (u1_struct_0 @ sk_B))) | 
% 0.38/0.58       ~
% 0.38/0.58       ((v1_funct_1 @ (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.38/0.58      inference('split', [status(esa)], ['32'])).
% 0.38/0.58  thf('122', plain,
% 0.38/0.58      (~
% 0.38/0.58       ((v5_pre_topc @ 
% 0.38/0.58         (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58         (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['62', '91', '120', '121'])).
% 0.38/0.58  thf('123', plain,
% 0.38/0.58      (~ (v5_pre_topc @ 
% 0.38/0.58          (k10_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.58          (k1_tsep_1 @ sk_A @ sk_C @ sk_D) @ sk_B)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['33', '122'])).
% 0.38/0.58  thf('124', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_D)
% 0.38/0.58        | (r1_tsep_1 @ sk_C @ sk_D)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['31', '123'])).
% 0.38/0.58  thf('125', plain, (~ (r1_tsep_1 @ sk_C @ sk_D)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('126', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_C)
% 0.38/0.58        | (v2_struct_0 @ sk_D)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['124', '125'])).
% 0.38/0.58  thf('127', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('128', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['126', '127'])).
% 0.38/0.58  thf('129', plain, (~ (v2_struct_0 @ sk_D)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('130', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.38/0.58      inference('clc', [status(thm)], ['128', '129'])).
% 0.38/0.58  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('132', plain, ((v2_struct_0 @ sk_C)),
% 0.38/0.58      inference('clc', [status(thm)], ['130', '131'])).
% 0.38/0.58  thf('133', plain, ($false), inference('demod', [status(thm)], ['0', '132'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
