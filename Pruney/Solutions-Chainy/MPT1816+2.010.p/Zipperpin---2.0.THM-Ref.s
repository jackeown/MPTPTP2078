%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rNVekP76QT

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:08 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  436 (2128 expanded)
%              Number of leaves         :   26 ( 620 expanded)
%              Depth                    :   27
%              Number of atoms          : 8175 (170448 expanded)
%              Number of equality atoms :   86 (1415 expanded)
%              Maximal formula depth    :   30 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t132_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                          & ( r4_tsep_1 @ A @ D @ E ) )
                       => ( ( ( v1_funct_1 @ C )
                            & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ C @ A @ B )
                            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( ( A
                              = ( k1_tsep_1 @ A @ D @ E ) )
                            & ( r4_tsep_1 @ A @ D @ E ) )
                         => ( ( ( v1_funct_1 @ C )
                              & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ C @ A @ B )
                              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                          <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                              & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_tmap_1])).

thf('0',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t126_tmap_1,axiom,(
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
                 => ( ( r4_tsep_1 @ A @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ C @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ D @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12','13','14','15','16'])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('20',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X7 )
      | ( ( k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) @ X8 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( k2_tmap_1 @ X2 @ X0 @ X3 @ X1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','56','57','58','59','60'])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','61'])).

thf('63',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('75',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('89',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95','96','97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['86','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48','49'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','115','116','117','118','119'])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['85','120'])).

thf('122',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('123',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('136',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ sk_E @ X0 )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','136'])).

thf('138',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ sk_E @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141','142','143','144','145'])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','146'])).

thf('148',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('149',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['147','148','149','150','151','152'])).

thf('154',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['132','153'])).

thf('155',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('156',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('169',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['167','169'])).

thf('171',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['170','171','172','173','174','175','176','177','178'])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['166','179'])).

thf('181',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('182',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['180','181','182','183','184','185'])).

thf('187',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['165','186'])).

thf('188',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('189',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('199',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('202',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['200','202'])).

thf('204',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204','205','206','207','208','209','210','211'])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['199','212'])).

thf('214',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('215',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['213','214','215','216','217','218'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['198','219'])).

thf('221',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['63'])).

thf('222',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('232',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ X13 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('235',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ X13 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ sk_D @ X0 )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['233','235'])).

thf('237',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['236','237','238','239','240','241','242','243','244'])).

thf('246',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['232','245'])).

thf('247',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('248',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['246','247','248','249','250','251'])).

thf('253',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['231','252'])).

thf('254',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('255',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['257','258'])).

thf('260',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['259','260'])).

thf('262',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('265',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('266',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('269',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['267','269'])).

thf('271',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['270','271','272','273','274','275','276','277','278'])).

thf('280',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['266','279'])).

thf('281',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['280','281','282','283','284'])).

thf('286',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['265','285'])).

thf('287',plain,
    ( ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['264','286'])).

thf('288',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['63'])).

thf('289',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['291','292'])).

thf('294',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['293','294'])).

thf('296',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('299',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('300',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('303',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['301','303'])).

thf('305',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['304','305','306','307','308','309','310','311','312'])).

thf('314',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_E )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['300','313'])).

thf('315',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['314','315','316','317','318'])).

thf('320',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['299','319'])).

thf('321',plain,
    ( ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['298','320'])).

thf('322',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['63'])).

thf('323',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['321','322'])).

thf('324',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('327',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['325','326'])).

thf('328',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['327','328'])).

thf('330',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['332','333','334','335'])).

thf('337',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['336'])).

thf('338',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['338'])).

thf('340',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['340'])).

thf('342',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['342'])).

thf('344',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['344'])).

thf('346',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['346'])).

thf('348',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['348'])).

thf('350',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['350'])).

thf('352',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['352'])).

thf('354',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('355',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ X13 @ X9 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X13 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ X10 @ X9 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ X11 @ X9 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X10 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v5_pre_topc @ X12 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ ( k1_tsep_1 @ X11 @ X13 @ X10 ) ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r4_tsep_1 @ X11 @ X13 @ X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t126_tmap_1])).

thf('357',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ sk_E @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['355','356'])).

thf('358',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('359',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('364',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('367',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('371',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('372',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('373',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ X1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ sk_E @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) )
      | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['357','358','359','360','361','362','363','364','365','366','367','368','369','370','371','372'])).

thf('374',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['354','373'])).

thf('375',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('378',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('379',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['39','55'])).

thf('380',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('381',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('382',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('383',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) ),
    inference('sup+',[status(thm)],['107','114'])).

thf('384',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['374','375','376','377','378','379','380','381','382','383','384','385','386'])).

thf('388',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['353','387'])).

thf('389',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['351','388'])).

thf('390',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['349','389'])).

thf('391',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['347','390'])).

thf('392',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['345','391'])).

thf('393',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['343','392'])).

thf('394',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['341','393'])).

thf('395',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['339','394'])).

thf('396',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('397',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['395','396'])).

thf('398',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['397','398'])).

thf('400',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('401',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['399','400'])).

thf('402',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('403',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      & ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      & ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['401','402'])).

thf('404',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('405',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['403','404'])).

thf('406',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('407',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['406'])).

thf('408',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','73','74','76','78','80','82','84','131','164','197','230','263','297','331','337','405','407'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rNVekP76QT
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:32:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 290 iterations in 0.134s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.61  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.43/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.43/0.61  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.43/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.61  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.43/0.61  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.43/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.61  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.43/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.61  thf(t132_tmap_1, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.43/0.61             ( l1_pre_topc @ B ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                 ( m1_subset_1 @
% 0.43/0.61                   C @ 
% 0.43/0.61                   ( k1_zfmisc_1 @
% 0.43/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.43/0.61               ( ![D:$i]:
% 0.43/0.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.43/0.61                   ( ![E:$i]:
% 0.43/0.61                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.43/0.61                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 0.43/0.61                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 0.43/0.61                         ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.61                             ( v1_funct_2 @
% 0.43/0.61                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                             ( v5_pre_topc @ C @ A @ B ) & 
% 0.43/0.61                             ( m1_subset_1 @
% 0.43/0.61                               C @ 
% 0.43/0.61                               ( k1_zfmisc_1 @
% 0.43/0.61                                 ( k2_zfmisc_1 @
% 0.43/0.61                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.43/0.61                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.43/0.61                             ( v1_funct_2 @
% 0.43/0.61                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.43/0.61                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                             ( v5_pre_topc @
% 0.43/0.61                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.43/0.61                             ( m1_subset_1 @
% 0.43/0.61                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.43/0.61                               ( k1_zfmisc_1 @
% 0.43/0.61                                 ( k2_zfmisc_1 @
% 0.43/0.61                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.43/0.61                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.43/0.61                             ( v1_funct_2 @
% 0.43/0.61                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.43/0.61                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                             ( v5_pre_topc @
% 0.43/0.61                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.43/0.61                             ( m1_subset_1 @
% 0.43/0.61                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.43/0.61                               ( k1_zfmisc_1 @
% 0.43/0.61                                 ( k2_zfmisc_1 @
% 0.43/0.61                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.43/0.61            ( l1_pre_topc @ A ) ) =>
% 0.43/0.61          ( ![B:$i]:
% 0.43/0.61            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.43/0.61                ( l1_pre_topc @ B ) ) =>
% 0.43/0.61              ( ![C:$i]:
% 0.43/0.61                ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.61                    ( v1_funct_2 @
% 0.43/0.61                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                    ( m1_subset_1 @
% 0.43/0.61                      C @ 
% 0.43/0.61                      ( k1_zfmisc_1 @
% 0.43/0.61                        ( k2_zfmisc_1 @
% 0.43/0.61                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.43/0.61                  ( ![D:$i]:
% 0.43/0.61                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.43/0.61                      ( ![E:$i]:
% 0.43/0.61                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.43/0.61                          ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 0.43/0.61                              ( r4_tsep_1 @ A @ D @ E ) ) =>
% 0.43/0.61                            ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.61                                ( v1_funct_2 @
% 0.43/0.61                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                                ( v5_pre_topc @ C @ A @ B ) & 
% 0.43/0.61                                ( m1_subset_1 @
% 0.43/0.61                                  C @ 
% 0.43/0.61                                  ( k1_zfmisc_1 @
% 0.43/0.61                                    ( k2_zfmisc_1 @
% 0.43/0.61                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.43/0.61                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.43/0.61                                ( v1_funct_2 @
% 0.43/0.61                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.43/0.61                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                                ( v5_pre_topc @
% 0.43/0.61                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 0.43/0.61                                ( m1_subset_1 @
% 0.43/0.61                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.43/0.61                                  ( k1_zfmisc_1 @
% 0.43/0.61                                    ( k2_zfmisc_1 @
% 0.43/0.61                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.43/0.61                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 0.43/0.61                                ( v1_funct_2 @
% 0.43/0.61                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.43/0.61                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                                ( v5_pre_topc @
% 0.43/0.61                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 0.43/0.61                                ( m1_subset_1 @
% 0.43/0.61                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.43/0.61                                  ( k1_zfmisc_1 @
% 0.43/0.61                                    ( k2_zfmisc_1 @
% 0.43/0.61                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t132_tmap_1])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61         (k1_zfmisc_1 @ 
% 0.43/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.43/0.61       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61         (k1_zfmisc_1 @ 
% 0.43/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.43/0.61      inference('split', [status(esa)], ['0'])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.43/0.61         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('split', [status(esa)], ['2'])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ 
% 0.43/0.61        (k1_zfmisc_1 @ 
% 0.43/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('5', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t126_tmap_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.43/0.61             ( l1_pre_topc @ B ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.43/0.61               ( ![D:$i]:
% 0.43/0.61                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.43/0.61                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 0.43/0.61                     ( ![E:$i]:
% 0.43/0.61                       ( ( ( v1_funct_1 @ E ) & 
% 0.43/0.61                           ( v1_funct_2 @
% 0.43/0.61                             E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.43/0.61                             ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                           ( m1_subset_1 @
% 0.43/0.61                             E @ 
% 0.43/0.61                             ( k1_zfmisc_1 @
% 0.43/0.61                               ( k2_zfmisc_1 @
% 0.43/0.61                                 ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.43/0.61                                 ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.43/0.61                         ( ( ( v1_funct_1 @ E ) & 
% 0.43/0.61                             ( v1_funct_2 @
% 0.43/0.61                               E @ 
% 0.43/0.61                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.43/0.61                               ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                             ( v5_pre_topc @ E @ ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 0.43/0.61                             ( m1_subset_1 @
% 0.43/0.61                               E @ 
% 0.43/0.61                               ( k1_zfmisc_1 @
% 0.43/0.61                                 ( k2_zfmisc_1 @
% 0.43/0.61                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 0.43/0.61                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 0.43/0.61                           ( ( v1_funct_1 @
% 0.43/0.61                               ( k3_tmap_1 @
% 0.43/0.61                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) ) & 
% 0.43/0.61                             ( v1_funct_2 @
% 0.43/0.61                               ( k3_tmap_1 @
% 0.43/0.61                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.43/0.61                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                             ( v5_pre_topc @
% 0.43/0.61                               ( k3_tmap_1 @
% 0.43/0.61                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.43/0.61                               C @ B ) & 
% 0.43/0.61                             ( m1_subset_1 @
% 0.43/0.61                               ( k3_tmap_1 @
% 0.43/0.61                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 0.43/0.61                               ( k1_zfmisc_1 @
% 0.43/0.61                                 ( k2_zfmisc_1 @
% 0.43/0.61                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.43/0.61                             ( v1_funct_1 @
% 0.43/0.61                               ( k3_tmap_1 @
% 0.43/0.61                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) ) & 
% 0.43/0.61                             ( v1_funct_2 @
% 0.43/0.61                               ( k3_tmap_1 @
% 0.43/0.61                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.43/0.61                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                             ( v5_pre_topc @
% 0.43/0.61                               ( k3_tmap_1 @
% 0.43/0.61                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.43/0.61                               D @ B ) & 
% 0.43/0.61                             ( m1_subset_1 @
% 0.43/0.61                               ( k3_tmap_1 @
% 0.43/0.61                                 A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 0.43/0.61                               ( k1_zfmisc_1 @
% 0.43/0.61                                 ( k2_zfmisc_1 @
% 0.43/0.61                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X9)
% 0.43/0.61          | ~ (v2_pre_topc @ X9)
% 0.43/0.61          | ~ (l1_pre_topc @ X9)
% 0.43/0.61          | (v2_struct_0 @ X10)
% 0.43/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.61          | ~ (v1_funct_1 @ X12)
% 0.43/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61               (u1_struct_0 @ X9))
% 0.43/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61                 (u1_struct_0 @ X9))))
% 0.43/0.61          | (m1_subset_1 @ 
% 0.43/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))))
% 0.43/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61                 (u1_struct_0 @ X9))))
% 0.43/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61               (u1_struct_0 @ X9))
% 0.43/0.61          | ~ (v1_funct_1 @ X12)
% 0.43/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.61          | (v2_struct_0 @ X13)
% 0.43/0.61          | ~ (l1_pre_topc @ X11)
% 0.43/0.61          | ~ (v2_pre_topc @ X11)
% 0.43/0.61          | (v2_struct_0 @ X11))),
% 0.43/0.61      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X11)
% 0.43/0.61          | ~ (v2_pre_topc @ X11)
% 0.43/0.61          | ~ (l1_pre_topc @ X11)
% 0.43/0.61          | (v2_struct_0 @ X13)
% 0.43/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.61          | (m1_subset_1 @ 
% 0.43/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))))
% 0.43/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61                 (u1_struct_0 @ X9))))
% 0.43/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61               (u1_struct_0 @ X9))
% 0.43/0.61          | ~ (v1_funct_1 @ X12)
% 0.43/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.61          | (v2_struct_0 @ X10)
% 0.43/0.61          | ~ (l1_pre_topc @ X9)
% 0.43/0.61          | ~ (v2_pre_topc @ X9)
% 0.43/0.61          | (v2_struct_0 @ X9))),
% 0.43/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ sk_E)
% 0.43/0.61          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.43/0.61          | ~ (v1_funct_1 @ X1)
% 0.43/0.61          | ~ (v1_funct_2 @ X1 @ 
% 0.43/0.61               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.61               (u1_struct_0 @ X0))
% 0.43/0.61          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.43/0.61          | (m1_subset_1 @ 
% 0.43/0.61             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.61              sk_D @ X1) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.43/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.43/0.61          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_D)
% 0.43/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '7'])).
% 0.43/0.61  thf('9', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('10', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('11', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('12', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('13', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('14', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ sk_E)
% 0.43/0.61          | ~ (v1_funct_1 @ X1)
% 0.43/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.43/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.43/0.61          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.43/0.61          | (v2_struct_0 @ sk_D)
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['8', '9', '10', '11', '12', '13', '14', '15', '16'])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_D)
% 0.43/0.61        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.43/0.61           (k1_zfmisc_1 @ 
% 0.43/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.61        | (v2_struct_0 @ sk_E)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_B)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_B)
% 0.43/0.61        | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '17'])).
% 0.43/0.61  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t2_tsep_1, axiom,
% 0.43/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ 
% 0.43/0.61        (k1_zfmisc_1 @ 
% 0.43/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d5_tmap_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.43/0.61             ( l1_pre_topc @ B ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( m1_pre_topc @ C @ A ) =>
% 0.43/0.61               ( ![D:$i]:
% 0.43/0.61                 ( ( m1_pre_topc @ D @ A ) =>
% 0.43/0.61                   ( ![E:$i]:
% 0.43/0.61                     ( ( ( v1_funct_1 @ E ) & 
% 0.43/0.61                         ( v1_funct_2 @
% 0.43/0.61                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                         ( m1_subset_1 @
% 0.43/0.61                           E @ 
% 0.43/0.61                           ( k1_zfmisc_1 @
% 0.43/0.61                             ( k2_zfmisc_1 @
% 0.43/0.61                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.43/0.61                       ( ( m1_pre_topc @ D @ C ) =>
% 0.43/0.61                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.43/0.61                           ( k2_partfun1 @
% 0.43/0.61                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.43/0.61                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X4)
% 0.43/0.61          | ~ (v2_pre_topc @ X4)
% 0.43/0.61          | ~ (l1_pre_topc @ X4)
% 0.43/0.61          | ~ (m1_pre_topc @ X5 @ X6)
% 0.43/0.61          | ~ (m1_pre_topc @ X5 @ X7)
% 0.43/0.61          | ((k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4) @ X8 @ 
% 0.43/0.61                 (u1_struct_0 @ X5)))
% 0.43/0.61          | ~ (m1_subset_1 @ X8 @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))))
% 0.43/0.61          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))
% 0.43/0.61          | ~ (v1_funct_1 @ X8)
% 0.43/0.61          | ~ (m1_pre_topc @ X7 @ X6)
% 0.43/0.61          | ~ (l1_pre_topc @ X6)
% 0.43/0.61          | ~ (v2_pre_topc @ X6)
% 0.43/0.61          | (v2_struct_0 @ X6))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.43/0.61          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.61          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61                 sk_C @ (u1_struct_0 @ X1)))
% 0.43/0.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.43/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.43/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.43/0.61          | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.61  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.43/0.61          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61                 sk_C @ (u1_struct_0 @ X1)))
% 0.43/0.61          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.43/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.43/0.61          | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_B)
% 0.43/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.43/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.43/0.61          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61                 sk_C @ (u1_struct_0 @ X0)))
% 0.43/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['20', '28'])).
% 0.43/0.61  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_B)
% 0.43/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.43/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.43/0.61          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61                 sk_C @ (u1_struct_0 @ X0)))
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61                 sk_C @ (u1_struct_0 @ X0)))
% 0.43/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('simplify', [status(thm)], ['33'])).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_B)
% 0.43/0.61        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.43/0.61            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61               sk_C @ (u1_struct_0 @ sk_D)))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['19', '34'])).
% 0.43/0.61  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.43/0.61            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61               sk_C @ (u1_struct_0 @ sk_D))))),
% 0.43/0.61      inference('clc', [status(thm)], ['35', '36'])).
% 0.43/0.61  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.43/0.61         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.43/0.61            (u1_struct_0 @ sk_D)))),
% 0.43/0.61      inference('clc', [status(thm)], ['37', '38'])).
% 0.43/0.61  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ 
% 0.43/0.61        (k1_zfmisc_1 @ 
% 0.43/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d4_tmap_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.43/0.61             ( l1_pre_topc @ B ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( ( v1_funct_1 @ C ) & 
% 0.43/0.61                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.43/0.61                 ( m1_subset_1 @
% 0.43/0.61                   C @ 
% 0.43/0.61                   ( k1_zfmisc_1 @
% 0.43/0.61                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.43/0.61               ( ![D:$i]:
% 0.43/0.61                 ( ( m1_pre_topc @ D @ A ) =>
% 0.43/0.61                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.43/0.61                     ( k2_partfun1 @
% 0.43/0.61                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.43/0.61                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | ~ (m1_pre_topc @ X1 @ X2)
% 0.43/0.61          | ((k2_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ 
% 0.43/0.61                 (u1_struct_0 @ X1)))
% 0.43/0.61          | ~ (m1_subset_1 @ X3 @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 0.43/0.61          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 0.43/0.61          | ~ (v1_funct_1 @ X3)
% 0.43/0.61          | ~ (l1_pre_topc @ X2)
% 0.43/0.61          | ~ (v2_pre_topc @ X2)
% 0.43/0.61          | (v2_struct_0 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.43/0.61          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.61          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61                 sk_C @ (u1_struct_0 @ X0)))
% 0.43/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.43/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.43/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.43/0.61          | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.43/0.61  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('49', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61                 sk_C @ (u1_struct_0 @ X0)))
% 0.43/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['43', '44', '45', '46', '47', '48', '49'])).
% 0.43/0.61  thf('51', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_B)
% 0.43/0.61        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.61            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61               sk_C @ (u1_struct_0 @ sk_D)))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['40', '50'])).
% 0.43/0.61  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.61            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61               sk_C @ (u1_struct_0 @ sk_D))))),
% 0.43/0.61      inference('clc', [status(thm)], ['51', '52'])).
% 0.43/0.61  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.61         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.43/0.61            (u1_struct_0 @ sk_D)))),
% 0.43/0.61      inference('clc', [status(thm)], ['53', '54'])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['39', '55'])).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('60', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_D)
% 0.43/0.61        | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61           (k1_zfmisc_1 @ 
% 0.43/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.61        | (v2_struct_0 @ sk_E)
% 0.43/0.61        | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['18', '56', '57', '58', '59', '60'])).
% 0.43/0.61  thf('62', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_B)
% 0.43/0.61         | (v2_struct_0 @ sk_E)
% 0.43/0.61         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61            (k1_zfmisc_1 @ 
% 0.43/0.61             (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61         | (v2_struct_0 @ sk_D)
% 0.43/0.61         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['3', '61'])).
% 0.43/0.61  thf('63', plain,
% 0.43/0.61      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61           (k1_zfmisc_1 @ 
% 0.43/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.61             sk_B)
% 0.43/0.61        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.61        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.61        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.61             sk_B)
% 0.43/0.61        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.61        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.61        | ~ (m1_subset_1 @ sk_C @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.61        | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61           (k1_zfmisc_1 @ 
% 0.43/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.61      inference('split', [status(esa)], ['63'])).
% 0.43/0.61  thf('65', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_A)
% 0.43/0.61         | (v2_struct_0 @ sk_D)
% 0.43/0.61         | (v2_struct_0 @ sk_E)
% 0.43/0.61         | (v2_struct_0 @ sk_B)))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['62', '64'])).
% 0.43/0.61  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('67', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['65', '66'])).
% 0.43/0.61  thf('68', plain, (~ (v2_struct_0 @ sk_E)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('69', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('clc', [status(thm)], ['67', '68'])).
% 0.43/0.61  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('71', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_D))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('clc', [status(thm)], ['69', '70'])).
% 0.43/0.61  thf('72', plain, (~ (v2_struct_0 @ sk_D)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('73', plain,
% 0.43/0.61      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.43/0.61       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61         (k1_zfmisc_1 @ 
% 0.43/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['71', '72'])).
% 0.43/0.61  thf('74', plain,
% 0.43/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.43/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('split', [status(esa)], ['2'])).
% 0.43/0.61  thf('75', plain,
% 0.43/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('76', plain,
% 0.43/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.61         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.43/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('split', [status(esa)], ['75'])).
% 0.43/0.61  thf('77', plain,
% 0.43/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.43/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('78', plain,
% 0.43/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.43/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('split', [status(esa)], ['77'])).
% 0.43/0.61  thf('79', plain,
% 0.43/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('80', plain,
% 0.43/0.61      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.43/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('split', [status(esa)], ['79'])).
% 0.43/0.61  thf('81', plain,
% 0.43/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('82', plain,
% 0.43/0.61      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.43/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('split', [status(esa)], ['81'])).
% 0.43/0.61  thf('83', plain,
% 0.43/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.43/0.61        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('84', plain,
% 0.43/0.61      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.43/0.61       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('split', [status(esa)], ['83'])).
% 0.43/0.61  thf('85', plain,
% 0.43/0.61      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.43/0.61         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('split', [status(esa)], ['2'])).
% 0.43/0.61  thf('86', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ 
% 0.43/0.61        (k1_zfmisc_1 @ 
% 0.43/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('87', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('88', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X9)
% 0.43/0.61          | ~ (v2_pre_topc @ X9)
% 0.43/0.61          | ~ (l1_pre_topc @ X9)
% 0.43/0.61          | (v2_struct_0 @ X10)
% 0.43/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.61          | ~ (v1_funct_1 @ X12)
% 0.43/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61               (u1_struct_0 @ X9))
% 0.43/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61                 (u1_struct_0 @ X9))))
% 0.43/0.61          | (m1_subset_1 @ 
% 0.43/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))))
% 0.43/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61                 (u1_struct_0 @ X9))))
% 0.43/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61               (u1_struct_0 @ X9))
% 0.43/0.61          | ~ (v1_funct_1 @ X12)
% 0.43/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.61          | (v2_struct_0 @ X13)
% 0.43/0.61          | ~ (l1_pre_topc @ X11)
% 0.43/0.61          | ~ (v2_pre_topc @ X11)
% 0.43/0.61          | (v2_struct_0 @ X11))),
% 0.43/0.61      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.43/0.61  thf('89', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X11)
% 0.43/0.61          | ~ (v2_pre_topc @ X11)
% 0.43/0.61          | ~ (l1_pre_topc @ X11)
% 0.43/0.61          | (v2_struct_0 @ X13)
% 0.43/0.61          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.61          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.61          | (m1_subset_1 @ 
% 0.43/0.61             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))))
% 0.43/0.61          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61                 (u1_struct_0 @ X9))))
% 0.43/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61               (u1_struct_0 @ X9))
% 0.43/0.61          | ~ (v1_funct_1 @ X12)
% 0.43/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.61          | (v2_struct_0 @ X10)
% 0.43/0.61          | ~ (l1_pre_topc @ X9)
% 0.43/0.61          | ~ (v2_pre_topc @ X9)
% 0.43/0.61          | (v2_struct_0 @ X9))),
% 0.43/0.61      inference('simplify', [status(thm)], ['88'])).
% 0.43/0.61  thf('90', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ sk_E)
% 0.43/0.61          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.43/0.61          | ~ (v1_funct_1 @ X1)
% 0.43/0.61          | ~ (v1_funct_2 @ X1 @ 
% 0.43/0.61               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.61               (u1_struct_0 @ X0))
% 0.43/0.61          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.43/0.61          | (m1_subset_1 @ 
% 0.43/0.61             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.61              sk_E @ X1) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 0.43/0.61          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.43/0.61          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_D)
% 0.43/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['87', '89'])).
% 0.43/0.61  thf('91', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('92', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('93', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('94', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('95', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('96', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('98', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('99', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.61          | (v2_struct_0 @ X0)
% 0.43/0.61          | ~ (v2_pre_topc @ X0)
% 0.43/0.61          | ~ (l1_pre_topc @ X0)
% 0.43/0.61          | (v2_struct_0 @ sk_E)
% 0.43/0.61          | ~ (v1_funct_1 @ X1)
% 0.43/0.61          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.43/0.61          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.43/0.61          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.43/0.61             (k1_zfmisc_1 @ 
% 0.43/0.61              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 0.43/0.61          | (v2_struct_0 @ sk_D)
% 0.43/0.61          | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['90', '91', '92', '93', '94', '95', '96', '97', '98'])).
% 0.43/0.61  thf('100', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_D)
% 0.43/0.61        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.43/0.61           (k1_zfmisc_1 @ 
% 0.43/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.61        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.61        | (v2_struct_0 @ sk_E)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_B)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_B)
% 0.43/0.61        | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['86', '99'])).
% 0.43/0.61  thf('101', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('102', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61                 sk_C @ (u1_struct_0 @ X0)))
% 0.43/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('simplify', [status(thm)], ['33'])).
% 0.43/0.61  thf('103', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_B)
% 0.43/0.61        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 0.43/0.61            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61               sk_C @ (u1_struct_0 @ sk_E)))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['101', '102'])).
% 0.43/0.61  thf('104', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('105', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 0.43/0.61            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61               sk_C @ (u1_struct_0 @ sk_E))))),
% 0.43/0.61      inference('clc', [status(thm)], ['103', '104'])).
% 0.43/0.61  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('107', plain,
% 0.43/0.61      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 0.43/0.61         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.43/0.61            (u1_struct_0 @ sk_E)))),
% 0.43/0.61      inference('clc', [status(thm)], ['105', '106'])).
% 0.43/0.61  thf('108', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('109', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((v2_struct_0 @ sk_A)
% 0.43/0.61          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.43/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61                 sk_C @ (u1_struct_0 @ X0)))
% 0.43/0.61          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.43/0.61          | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['43', '44', '45', '46', '47', '48', '49'])).
% 0.43/0.61  thf('110', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_B)
% 0.43/0.61        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.61            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61               sk_C @ (u1_struct_0 @ sk_E)))
% 0.43/0.61        | (v2_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['108', '109'])).
% 0.43/0.61  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('112', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.61            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.43/0.61               sk_C @ (u1_struct_0 @ sk_E))))),
% 0.43/0.61      inference('clc', [status(thm)], ['110', '111'])).
% 0.43/0.61  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('114', plain,
% 0.43/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.61         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.43/0.61            (u1_struct_0 @ sk_E)))),
% 0.43/0.61      inference('clc', [status(thm)], ['112', '113'])).
% 0.43/0.61  thf('115', plain,
% 0.43/0.61      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.61         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.43/0.61      inference('sup+', [status(thm)], ['107', '114'])).
% 0.43/0.61  thf('116', plain,
% 0.43/0.61      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('118', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('119', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('120', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_A)
% 0.43/0.61        | (v2_struct_0 @ sk_D)
% 0.43/0.61        | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61           (k1_zfmisc_1 @ 
% 0.43/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.61        | (v2_struct_0 @ sk_E)
% 0.43/0.61        | (v2_struct_0 @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)],
% 0.43/0.61                ['100', '115', '116', '117', '118', '119'])).
% 0.43/0.61  thf('121', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_B)
% 0.43/0.61         | (v2_struct_0 @ sk_E)
% 0.43/0.61         | (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61            (k1_zfmisc_1 @ 
% 0.43/0.61             (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.61         | (v2_struct_0 @ sk_D)
% 0.43/0.61         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['85', '120'])).
% 0.43/0.61  thf('122', plain,
% 0.43/0.61      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61           (k1_zfmisc_1 @ 
% 0.43/0.61            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.61      inference('split', [status(esa)], ['63'])).
% 0.43/0.61  thf('123', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_A)
% 0.43/0.61         | (v2_struct_0 @ sk_D)
% 0.43/0.61         | (v2_struct_0 @ sk_E)
% 0.43/0.61         | (v2_struct_0 @ sk_B)))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['121', '122'])).
% 0.43/0.61  thf('124', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('125', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['123', '124'])).
% 0.43/0.61  thf('126', plain, (~ (v2_struct_0 @ sk_E)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('127', plain,
% 0.43/0.61      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('clc', [status(thm)], ['125', '126'])).
% 0.43/0.61  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('129', plain,
% 0.43/0.61      (((v2_struct_0 @ sk_D))
% 0.43/0.61         <= (~
% 0.43/0.61             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61               (k1_zfmisc_1 @ 
% 0.43/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.61             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('clc', [status(thm)], ['127', '128'])).
% 0.43/0.61  thf('130', plain, (~ (v2_struct_0 @ sk_D)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('131', plain,
% 0.43/0.61      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.61         (k1_zfmisc_1 @ 
% 0.43/0.61          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.43/0.61       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['129', '130'])).
% 0.43/0.61  thf('132', plain,
% 0.43/0.61      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.43/0.61         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.61      inference('split', [status(esa)], ['2'])).
% 0.43/0.61  thf('133', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_C @ 
% 0.43/0.61        (k1_zfmisc_1 @ 
% 0.43/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('134', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('135', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.61         ((v2_struct_0 @ X9)
% 0.43/0.61          | ~ (v2_pre_topc @ X9)
% 0.43/0.61          | ~ (l1_pre_topc @ X9)
% 0.43/0.61          | (v2_struct_0 @ X10)
% 0.43/0.61          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.61          | ~ (v1_funct_1 @ X12)
% 0.43/0.61          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.61               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.61               (u1_struct_0 @ X9))
% 0.43/0.61          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | (v5_pre_topc @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.43/0.62             X10 @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.43/0.62  thf('136', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | (v5_pre_topc @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.43/0.62             X10 @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X9))),
% 0.43/0.62      inference('simplify', [status(thm)], ['135'])).
% 0.43/0.62  thf('137', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.62               (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.43/0.62          | (v5_pre_topc @ 
% 0.43/0.62             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62              sk_E @ X1) @ 
% 0.43/0.62             sk_E @ X0)
% 0.43/0.62          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['134', '136'])).
% 0.43/0.62  thf('138', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('139', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('140', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('141', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('142', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('143', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('145', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('146', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.43/0.62          | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ sk_E @ 
% 0.43/0.62             X0)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['137', '138', '139', '140', '141', '142', '143', '144', '145'])).
% 0.43/0.62  thf('147', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.43/0.62           sk_E @ sk_B)
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_B)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['133', '146'])).
% 0.43/0.62  thf('148', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['107', '114'])).
% 0.43/0.62  thf('149', plain,
% 0.43/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('151', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('152', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('153', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['147', '148', '149', '150', '151', '152'])).
% 0.43/0.62  thf('154', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['132', '153'])).
% 0.43/0.62  thf('155', plain,
% 0.43/0.62      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['63'])).
% 0.43/0.62  thf('156', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['154', '155'])).
% 0.43/0.62  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('158', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['156', '157'])).
% 0.43/0.62  thf('159', plain, (~ (v2_struct_0 @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('160', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['158', '159'])).
% 0.43/0.62  thf('161', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('162', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_D))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['160', '161'])).
% 0.43/0.62  thf('163', plain, (~ (v2_struct_0 @ sk_D)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('164', plain,
% 0.43/0.62      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.43/0.62       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['162', '163'])).
% 0.43/0.62  thf('165', plain,
% 0.43/0.62      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.43/0.62         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf('166', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ 
% 0.43/0.62        (k1_zfmisc_1 @ 
% 0.43/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('167', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('168', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | (v1_funct_2 @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.43/0.62             (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.43/0.62  thf('169', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | (v1_funct_2 @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12) @ 
% 0.43/0.62             (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X9))),
% 0.43/0.62      inference('simplify', [status(thm)], ['168'])).
% 0.43/0.62  thf('170', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.62               (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.43/0.62          | (v1_funct_2 @ 
% 0.43/0.62             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62              sk_E @ X1) @ 
% 0.43/0.62             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['167', '169'])).
% 0.43/0.62  thf('171', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('172', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('173', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('174', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('175', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('176', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('178', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('179', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.43/0.62          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.43/0.62             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['170', '171', '172', '173', '174', '175', '176', '177', '178'])).
% 0.43/0.62  thf('180', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.43/0.62           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_B)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['166', '179'])).
% 0.43/0.62  thf('181', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['107', '114'])).
% 0.43/0.62  thf('182', plain,
% 0.43/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('184', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('185', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('186', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['180', '181', '182', '183', '184', '185'])).
% 0.43/0.62  thf('187', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62            (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['165', '186'])).
% 0.43/0.62  thf('188', plain,
% 0.43/0.62      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('split', [status(esa)], ['63'])).
% 0.43/0.62  thf('189', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['187', '188'])).
% 0.43/0.62  thf('190', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('191', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['189', '190'])).
% 0.43/0.62  thf('192', plain, (~ (v2_struct_0 @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('193', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['191', '192'])).
% 0.43/0.62  thf('194', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('195', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_D))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['193', '194'])).
% 0.43/0.62  thf('196', plain, (~ (v2_struct_0 @ sk_D)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('197', plain,
% 0.43/0.62      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.43/0.62       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['195', '196'])).
% 0.43/0.62  thf('198', plain,
% 0.43/0.62      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.43/0.62         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf('199', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ 
% 0.43/0.62        (k1_zfmisc_1 @ 
% 0.43/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('200', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('201', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | (v1_funct_2 @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.43/0.62             (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.43/0.62  thf('202', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | (v1_funct_2 @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.43/0.62             (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X9))),
% 0.43/0.62      inference('simplify', [status(thm)], ['201'])).
% 0.43/0.62  thf('203', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.62               (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.43/0.62          | (v1_funct_2 @ 
% 0.43/0.62             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62              sk_D @ X1) @ 
% 0.43/0.62             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['200', '202'])).
% 0.43/0.62  thf('204', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('205', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('206', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('207', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('208', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('209', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('210', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('211', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('212', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.43/0.62          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.43/0.62             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['203', '204', '205', '206', '207', '208', '209', '210', '211'])).
% 0.43/0.62  thf('213', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.43/0.62           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_B)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['199', '212'])).
% 0.43/0.62  thf('214', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['39', '55'])).
% 0.43/0.62  thf('215', plain,
% 0.43/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('217', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('218', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('219', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['213', '214', '215', '216', '217', '218'])).
% 0.43/0.62  thf('220', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62            (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['198', '219'])).
% 0.43/0.62  thf('221', plain,
% 0.43/0.62      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('split', [status(esa)], ['63'])).
% 0.43/0.62  thf('222', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['220', '221'])).
% 0.43/0.62  thf('223', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('224', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['222', '223'])).
% 0.43/0.62  thf('225', plain, (~ (v2_struct_0 @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('226', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['224', '225'])).
% 0.43/0.62  thf('227', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('228', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_D))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['226', '227'])).
% 0.43/0.62  thf('229', plain, (~ (v2_struct_0 @ sk_D)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('230', plain,
% 0.43/0.62      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.43/0.62       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['228', '229'])).
% 0.43/0.62  thf('231', plain,
% 0.43/0.62      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.43/0.62         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf('232', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ 
% 0.43/0.62        (k1_zfmisc_1 @ 
% 0.43/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('233', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('234', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | (v5_pre_topc @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.43/0.62             X13 @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.43/0.62  thf('235', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | (v5_pre_topc @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12) @ 
% 0.43/0.62             X13 @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X9))),
% 0.43/0.62      inference('simplify', [status(thm)], ['234'])).
% 0.43/0.62  thf('236', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.62               (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.43/0.62          | (v5_pre_topc @ 
% 0.43/0.62             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62              sk_D @ X1) @ 
% 0.43/0.62             sk_D @ X0)
% 0.43/0.62          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['233', '235'])).
% 0.43/0.62  thf('237', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('238', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('239', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('240', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('241', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('242', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('243', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('244', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('245', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.43/0.62          | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ sk_D @ 
% 0.43/0.62             X0)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['236', '237', '238', '239', '240', '241', '242', '243', '244'])).
% 0.43/0.62  thf('246', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.43/0.62           sk_D @ sk_B)
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_B)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['232', '245'])).
% 0.43/0.62  thf('247', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['39', '55'])).
% 0.43/0.62  thf('248', plain,
% 0.43/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('249', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('250', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('251', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('252', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['246', '247', '248', '249', '250', '251'])).
% 0.43/0.62  thf('253', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['231', '252'])).
% 0.43/0.62  thf('254', plain,
% 0.43/0.62      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['63'])).
% 0.43/0.62  thf('255', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['253', '254'])).
% 0.43/0.62  thf('256', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('257', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['255', '256'])).
% 0.43/0.62  thf('258', plain, (~ (v2_struct_0 @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('259', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['257', '258'])).
% 0.43/0.62  thf('260', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('261', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_D))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['259', '260'])).
% 0.43/0.62  thf('262', plain, (~ (v2_struct_0 @ sk_D)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('263', plain,
% 0.43/0.62      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.43/0.62       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['261', '262'])).
% 0.43/0.62  thf('264', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['107', '114'])).
% 0.43/0.62  thf('265', plain,
% 0.43/0.62      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.43/0.62         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf('266', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ 
% 0.43/0.62        (k1_zfmisc_1 @ 
% 0.43/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('267', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('268', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | (v1_funct_1 @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12))
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.43/0.62  thf('269', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | (v1_funct_1 @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ X12))
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X9))),
% 0.43/0.62      inference('simplify', [status(thm)], ['268'])).
% 0.43/0.62  thf('270', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.62               (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.43/0.62          | (v1_funct_1 @ 
% 0.43/0.62             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62              sk_E @ X1))
% 0.43/0.62          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['267', '269'])).
% 0.43/0.62  thf('271', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('272', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('273', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('274', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('275', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('276', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('277', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('278', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('279', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.43/0.62          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1))
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['270', '271', '272', '273', '274', '275', '276', '277', '278'])).
% 0.43/0.62  thf('280', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_B)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['266', '279'])).
% 0.43/0.62  thf('281', plain,
% 0.43/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('282', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('283', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('284', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('285', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)], ['280', '281', '282', '283', '284'])).
% 0.43/0.62  thf('286', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['265', '285'])).
% 0.43/0.62  thf('287', plain,
% 0.43/0.62      ((((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['264', '286'])).
% 0.43/0.62  thf('288', plain,
% 0.43/0.62      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.43/0.62      inference('split', [status(esa)], ['63'])).
% 0.43/0.62  thf('289', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['287', '288'])).
% 0.43/0.62  thf('290', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('291', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['289', '290'])).
% 0.43/0.62  thf('292', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('293', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['291', '292'])).
% 0.43/0.62  thf('294', plain, (~ (v2_struct_0 @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('295', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_D))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['293', '294'])).
% 0.43/0.62  thf('296', plain, (~ (v2_struct_0 @ sk_D)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('297', plain,
% 0.43/0.62      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.43/0.62       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['295', '296'])).
% 0.43/0.62  thf('298', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['39', '55'])).
% 0.43/0.62  thf('299', plain,
% 0.43/0.62      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.43/0.62         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['2'])).
% 0.43/0.62  thf('300', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ 
% 0.43/0.62        (k1_zfmisc_1 @ 
% 0.43/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('301', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('302', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | (v1_funct_1 @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12))
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.43/0.62  thf('303', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | (v1_funct_1 @ 
% 0.43/0.62             (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ X12))
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X9))),
% 0.43/0.62      inference('simplify', [status(thm)], ['302'])).
% 0.43/0.62  thf('304', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.62               (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.43/0.62          | (v1_funct_1 @ 
% 0.43/0.62             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62              sk_D @ X1))
% 0.43/0.62          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['301', '303'])).
% 0.43/0.62  thf('305', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('306', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('307', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('308', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('309', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('310', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('311', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('312', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('313', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X1 @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.43/0.62          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1))
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['304', '305', '306', '307', '308', '309', '310', '311', '312'])).
% 0.43/0.62  thf('314', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_B)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['300', '313'])).
% 0.43/0.62  thf('315', plain,
% 0.43/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('316', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('317', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('318', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('319', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | (v2_struct_0 @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)], ['314', '315', '316', '317', '318'])).
% 0.43/0.62  thf('320', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['299', '319'])).
% 0.43/0.62  thf('321', plain,
% 0.43/0.62      ((((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['298', '320'])).
% 0.43/0.62  thf('322', plain,
% 0.43/0.62      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.43/0.62      inference('split', [status(esa)], ['63'])).
% 0.43/0.62  thf('323', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['321', '322'])).
% 0.43/0.62  thf('324', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('325', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['323', '324'])).
% 0.43/0.62  thf('326', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('327', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['325', '326'])).
% 0.43/0.62  thf('328', plain, (~ (v2_struct_0 @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('329', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_D))
% 0.43/0.62         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('clc', [status(thm)], ['327', '328'])).
% 0.43/0.62  thf('330', plain, (~ (v2_struct_0 @ sk_D)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('331', plain,
% 0.43/0.62      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.43/0.62       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['329', '330'])).
% 0.43/0.62  thf('332', plain,
% 0.43/0.62      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62           (k1_zfmisc_1 @ 
% 0.43/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62             sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62             sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62        | ~ (m1_subset_1 @ sk_C @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('333', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ 
% 0.43/0.62        (k1_zfmisc_1 @ 
% 0.43/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('334', plain,
% 0.43/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('335', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('336', plain,
% 0.43/0.62      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62           (k1_zfmisc_1 @ 
% 0.43/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62             sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62             sk_B)
% 0.43/0.62        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('demod', [status(thm)], ['332', '333', '334', '335'])).
% 0.43/0.62  thf('337', plain,
% 0.43/0.62      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 0.43/0.62       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.43/0.62       ~
% 0.43/0.62       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.43/0.62       ~
% 0.43/0.62       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.43/0.62       ~
% 0.43/0.62       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.43/0.62       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.43/0.62       ~
% 0.43/0.62       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.43/0.62       ~
% 0.43/0.62       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.43/0.62       ~
% 0.43/0.62       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['336'])).
% 0.43/0.62  thf('338', plain,
% 0.43/0.62      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62        | (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('339', plain,
% 0.43/0.62      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.43/0.62         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 0.43/0.62      inference('split', [status(esa)], ['338'])).
% 0.43/0.62  thf('340', plain,
% 0.43/0.62      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62        | (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('341', plain,
% 0.43/0.62      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.43/0.62         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.43/0.62      inference('split', [status(esa)], ['340'])).
% 0.43/0.62  thf('342', plain,
% 0.43/0.62      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 0.43/0.62        | (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('343', plain,
% 0.43/0.62      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 0.43/0.62         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['342'])).
% 0.43/0.62  thf('344', plain,
% 0.43/0.62      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 0.43/0.62        | (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('345', plain,
% 0.43/0.62      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 0.43/0.62         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['344'])).
% 0.43/0.62  thf('346', plain,
% 0.43/0.62      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('347', plain,
% 0.43/0.62      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 0.43/0.62         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('split', [status(esa)], ['346'])).
% 0.43/0.62  thf('348', plain,
% 0.43/0.62      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('349', plain,
% 0.43/0.62      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.43/0.62         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('split', [status(esa)], ['348'])).
% 0.43/0.62  thf('350', plain,
% 0.43/0.62      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('351', plain,
% 0.43/0.62      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 0.43/0.62         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('split', [status(esa)], ['350'])).
% 0.43/0.62  thf('352', plain,
% 0.43/0.62      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | (v1_funct_1 @ sk_C))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('353', plain,
% 0.43/0.62      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.43/0.62         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('split', [status(esa)], ['352'])).
% 0.43/0.62  thf('354', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['39', '55'])).
% 0.43/0.62  thf('355', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('356', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.62         ((v2_struct_0 @ X9)
% 0.43/0.62          | ~ (v2_pre_topc @ X9)
% 0.43/0.62          | ~ (l1_pre_topc @ X9)
% 0.43/0.62          | (v2_struct_0 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X10 @ X11)
% 0.43/0.62          | ~ (v1_funct_1 @ 
% 0.43/0.62               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.43/0.62                X12))
% 0.43/0.62          | ~ (v1_funct_2 @ 
% 0.43/0.62               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.43/0.62                X12) @ 
% 0.43/0.62               (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v5_pre_topc @ 
% 0.43/0.62               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.43/0.62                X12) @ 
% 0.43/0.62               X13 @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ 
% 0.43/0.62               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X13 @ 
% 0.43/0.62                X12) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v1_funct_1 @ 
% 0.43/0.62               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.43/0.62                X12))
% 0.43/0.62          | ~ (v1_funct_2 @ 
% 0.43/0.62               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.43/0.62                X12) @ 
% 0.43/0.62               (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v5_pre_topc @ 
% 0.43/0.62               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.43/0.62                X12) @ 
% 0.43/0.62               X10 @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ 
% 0.43/0.62               (k3_tmap_1 @ X11 @ X9 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X10 @ 
% 0.43/0.62                X12) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))))
% 0.43/0.62          | (v5_pre_topc @ X12 @ (k1_tsep_1 @ X11 @ X13 @ X10) @ X9)
% 0.43/0.62          | ~ (m1_subset_1 @ X12 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62                 (u1_struct_0 @ X9))))
% 0.43/0.62          | ~ (v1_funct_2 @ X12 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ X11 @ X13 @ X10)) @ 
% 0.43/0.62               (u1_struct_0 @ X9))
% 0.43/0.62          | ~ (v1_funct_1 @ X12)
% 0.43/0.62          | ~ (r4_tsep_1 @ X11 @ X13 @ X10)
% 0.43/0.62          | ~ (m1_pre_topc @ X13 @ X11)
% 0.43/0.62          | (v2_struct_0 @ X13)
% 0.43/0.62          | ~ (l1_pre_topc @ X11)
% 0.43/0.62          | ~ (v2_pre_topc @ X11)
% 0.43/0.62          | (v2_struct_0 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [t126_tmap_1])).
% 0.43/0.62  thf('357', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ sk_A)
% 0.43/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.43/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.43/0.62          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ 
% 0.43/0.62               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.62               (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (m1_subset_1 @ X1 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ 
% 0.43/0.62                 (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.43/0.62                 (u1_struct_0 @ X0))))
% 0.43/0.62          | (v5_pre_topc @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 0.43/0.62          | ~ (m1_subset_1 @ 
% 0.43/0.62               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62                sk_E @ X1) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | ~ (v5_pre_topc @ 
% 0.43/0.62               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62                sk_E @ X1) @ 
% 0.43/0.62               sk_E @ X0)
% 0.43/0.62          | ~ (v1_funct_2 @ 
% 0.43/0.62               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62                sk_E @ X1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v1_funct_1 @ 
% 0.43/0.62               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62                sk_E @ X1))
% 0.43/0.62          | ~ (v5_pre_topc @ 
% 0.43/0.62               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62                sk_D @ X1) @ 
% 0.43/0.62               sk_D @ X0)
% 0.43/0.62          | ~ (v1_funct_2 @ 
% 0.43/0.62               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62                sk_D @ X1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v1_funct_1 @ 
% 0.43/0.62               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 0.43/0.62                sk_D @ X1))
% 0.43/0.62          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['355', '356'])).
% 0.43/0.62  thf('358', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('359', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('360', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('361', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('362', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('363', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('364', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('365', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('366', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('367', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('368', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('369', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('370', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('371', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('372', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('373', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v2_struct_0 @ sk_A)
% 0.43/0.62          | (v2_struct_0 @ sk_D)
% 0.43/0.62          | ~ (v1_funct_1 @ X1)
% 0.43/0.62          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (m1_subset_1 @ X1 @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | (v5_pre_topc @ X1 @ sk_A @ X0)
% 0.43/0.62          | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))))
% 0.43/0.62          | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.43/0.62               sk_E @ X0)
% 0.43/0.62          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1))
% 0.43/0.62          | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.43/0.62               sk_D @ X0)
% 0.43/0.62          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1))
% 0.43/0.62          | (v2_struct_0 @ sk_E)
% 0.43/0.62          | ~ (l1_pre_topc @ X0)
% 0.43/0.62          | ~ (v2_pre_topc @ X0)
% 0.43/0.62          | (v2_struct_0 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['357', '358', '359', '360', '361', '362', '363', '364', 
% 0.43/0.62                 '365', '366', '367', '368', '369', '370', '371', '372'])).
% 0.43/0.62  thf('374', plain,
% 0.43/0.62      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62           (k1_zfmisc_1 @ 
% 0.43/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | (v2_struct_0 @ sk_B)
% 0.43/0.62        | ~ (v2_pre_topc @ sk_B)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))
% 0.43/0.62        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.43/0.62             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ 
% 0.43/0.62             sk_D @ sk_B)
% 0.43/0.62        | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))
% 0.43/0.62        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.43/0.62             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.43/0.62             sk_E @ sk_B)
% 0.43/0.62        | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | ~ (m1_subset_1 @ sk_C @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['354', '373'])).
% 0.43/0.62  thf('375', plain, ((v2_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('376', plain, ((l1_pre_topc @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('377', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['39', '55'])).
% 0.43/0.62  thf('378', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['39', '55'])).
% 0.43/0.62  thf('379', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['39', '55'])).
% 0.43/0.62  thf('380', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['107', '114'])).
% 0.43/0.62  thf('381', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['107', '114'])).
% 0.43/0.62  thf('382', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['107', '114'])).
% 0.43/0.62  thf('383', plain,
% 0.43/0.62      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.43/0.62         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))),
% 0.43/0.62      inference('sup+', [status(thm)], ['107', '114'])).
% 0.43/0.62  thf('384', plain,
% 0.43/0.62      ((m1_subset_1 @ sk_C @ 
% 0.43/0.62        (k1_zfmisc_1 @ 
% 0.43/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('385', plain,
% 0.43/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('386', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('387', plain,
% 0.43/0.62      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62           (k1_zfmisc_1 @ 
% 0.43/0.62            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | (v2_struct_0 @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_E)
% 0.43/0.62        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62             sk_B)
% 0.43/0.62        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62             sk_B)
% 0.43/0.62        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62             (k1_zfmisc_1 @ 
% 0.43/0.62              (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62        | (v2_struct_0 @ sk_D)
% 0.43/0.62        | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)],
% 0.43/0.62                ['374', '375', '376', '377', '378', '379', '380', '381', 
% 0.43/0.62                 '382', '383', '384', '385', '386'])).
% 0.43/0.62  thf('388', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62         | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62              (k1_zfmisc_1 @ 
% 0.43/0.62               (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62              sk_B)
% 0.43/0.62         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62              sk_B)
% 0.43/0.62         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B)))
% 0.43/0.62         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['353', '387'])).
% 0.43/0.62  thf('389', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62              (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.43/0.62         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62              sk_B)
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62              sk_B)
% 0.43/0.62         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['351', '388'])).
% 0.43/0.62  thf('390', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62              sk_B)
% 0.43/0.62         | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62              (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62              sk_B)
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B)))
% 0.43/0.62         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['349', '389'])).
% 0.43/0.62  thf('391', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62              sk_B)
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62              sk_B)
% 0.43/0.62         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['347', '390'])).
% 0.43/0.62  thf('392', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62              sk_B)
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B)))
% 0.43/0.62         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['345', '391'])).
% 0.43/0.62  thf('393', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['343', '392'])).
% 0.43/0.62  thf('394', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62         | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B)))
% 0.43/0.62         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['341', '393'])).
% 0.43/0.62  thf('395', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['339', '394'])).
% 0.43/0.62  thf('396', plain,
% 0.43/0.62      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 0.43/0.62         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['63'])).
% 0.43/0.62  thf('397', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A)
% 0.43/0.62         | (v2_struct_0 @ sk_D)
% 0.43/0.62         | (v2_struct_0 @ sk_E)
% 0.43/0.62         | (v2_struct_0 @ sk_B)))
% 0.43/0.62         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.43/0.62             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['395', '396'])).
% 0.43/0.62  thf('398', plain, (~ (v2_struct_0 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('399', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.43/0.62             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['397', '398'])).
% 0.43/0.62  thf('400', plain, (~ (v2_struct_0 @ sk_E)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('401', plain,
% 0.43/0.62      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D)))
% 0.43/0.62         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.43/0.62             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('clc', [status(thm)], ['399', '400'])).
% 0.43/0.62  thf('402', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('403', plain,
% 0.43/0.62      (((v2_struct_0 @ sk_D))
% 0.43/0.62         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 0.43/0.62             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) & 
% 0.43/0.62             ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) & 
% 0.43/0.62             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) & 
% 0.43/0.62             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 0.43/0.62               sk_B)) & 
% 0.43/0.62             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62               (k1_zfmisc_1 @ 
% 0.43/0.62                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 0.43/0.62      inference('clc', [status(thm)], ['401', '402'])).
% 0.43/0.62  thf('404', plain, (~ (v2_struct_0 @ sk_D)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('405', plain,
% 0.43/0.62      (~
% 0.43/0.62       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))) | 
% 0.43/0.62       ~
% 0.43/0.62       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 0.43/0.62       ~
% 0.43/0.62       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.43/0.62       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))) | 
% 0.43/0.62       ~
% 0.43/0.62       ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.43/0.62       ~
% 0.43/0.62       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 0.43/0.62       ~
% 0.43/0.62       ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.43/0.62         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))) | 
% 0.43/0.62       ~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))) | 
% 0.43/0.62       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['403', '404'])).
% 0.43/0.62  thf('406', plain,
% 0.43/0.62      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 0.43/0.62        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('407', plain,
% 0.43/0.62      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.43/0.62         (k1_zfmisc_1 @ 
% 0.43/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))) | 
% 0.43/0.62       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 0.43/0.62      inference('split', [status(esa)], ['406'])).
% 0.43/0.62  thf('408', plain, ($false),
% 0.43/0.62      inference('sat_resolution*', [status(thm)],
% 0.43/0.62                ['1', '73', '74', '76', '78', '80', '82', '84', '131', '164', 
% 0.43/0.62                 '197', '230', '263', '297', '331', '337', '405', '407'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
