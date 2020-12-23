%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wjJU18PRaK

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:05 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 235 expanded)
%              Number of leaves         :   37 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          : 1351 (7883 expanded)
%              Number of equality atoms :   37 ( 127 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t76_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                           => ( ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F ) @ ( u1_struct_0 @ C ) )
                             => ( ( k8_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                = ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                             => ( ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F ) @ ( u1_struct_0 @ C ) )
                               => ( ( k8_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                  = ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tmap_1])).

thf('0',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( ( k8_relset_1 @ X5 @ X6 @ X4 @ X7 )
        = ( k10_relat_1 @ X4 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k10_relat_1 @ sk_E @ sk_F )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( ( k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) @ X28 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k2_partfun1 @ X9 @ X10 @ X8 @ X11 )
        = ( k7_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10','11','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('31',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( ( k2_tmap_1 @ X22 @ X20 @ X23 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) @ X23 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('50',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','41','46','47','48','49','50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_struct_0 @ X31 )
      | ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X32 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X30 @ X31 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X31 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['44','45'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['57','71'])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['31','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ( ( k8_relset_1 @ X5 @ X6 @ X4 @ X7 )
        = ( k10_relat_1 @ X4 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('84',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf(t175_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X12 @ X13 ) @ X14 )
      | ( ( k10_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X12 @ X14 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t175_funct_2])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( ( k10_relat_1 @ sk_E @ sk_F )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('91',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k10_relat_1 @ sk_E @ sk_F )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['86','91','92'])).

thf('94',plain,(
    ( k10_relat_1 @ sk_E @ sk_F )
 != ( k10_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['4','30','81','93'])).

thf('95',plain,(
    $false ),
    inference(simplify,[status(thm)],['94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wjJU18PRaK
% 0.13/0.37  % Computer   : n022.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:50:11 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.47  % Solved by: fo/fo7.sh
% 0.24/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.47  % done 71 iterations in 0.026s
% 0.24/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.47  % SZS output start Refutation
% 0.24/0.47  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.24/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.24/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.24/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.47  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.24/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.24/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.47  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.24/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.24/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.24/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.24/0.47  thf(t76_tmap_1, conjecture,
% 0.24/0.47    (![A:$i]:
% 0.24/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.47       ( ![B:$i]:
% 0.24/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.24/0.47             ( l1_pre_topc @ B ) ) =>
% 0.24/0.47           ( ![C:$i]:
% 0.24/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.47               ( ![D:$i]:
% 0.24/0.47                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.24/0.47                   ( ![E:$i]:
% 0.24/0.47                     ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.47                         ( v1_funct_2 @
% 0.24/0.47                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.47                         ( m1_subset_1 @
% 0.24/0.47                           E @ 
% 0.24/0.47                           ( k1_zfmisc_1 @
% 0.24/0.47                             ( k2_zfmisc_1 @
% 0.24/0.47                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.47                       ( ( m1_pre_topc @ C @ D ) =>
% 0.24/0.47                         ( ![F:$i]:
% 0.24/0.47                           ( ( m1_subset_1 @
% 0.24/0.47                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.24/0.47                             ( ( r1_tarski @
% 0.24/0.47                                 ( k8_relset_1 @
% 0.24/0.47                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.24/0.47                                   E @ F ) @ 
% 0.24/0.47                                 ( u1_struct_0 @ C ) ) =>
% 0.24/0.47                               ( ( k8_relset_1 @
% 0.24/0.47                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.24/0.47                                   E @ F ) =
% 0.24/0.47                                 ( k8_relset_1 @
% 0.24/0.47                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.24/0.47                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.47    (~( ![A:$i]:
% 0.24/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.47            ( l1_pre_topc @ A ) ) =>
% 0.24/0.47          ( ![B:$i]:
% 0.24/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.24/0.47                ( l1_pre_topc @ B ) ) =>
% 0.24/0.47              ( ![C:$i]:
% 0.24/0.47                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.47                  ( ![D:$i]:
% 0.24/0.47                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.24/0.47                      ( ![E:$i]:
% 0.24/0.47                        ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.47                            ( v1_funct_2 @
% 0.24/0.47                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.47                            ( m1_subset_1 @
% 0.24/0.47                              E @ 
% 0.24/0.47                              ( k1_zfmisc_1 @
% 0.24/0.47                                ( k2_zfmisc_1 @
% 0.24/0.47                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.47                          ( ( m1_pre_topc @ C @ D ) =>
% 0.24/0.47                            ( ![F:$i]:
% 0.24/0.47                              ( ( m1_subset_1 @
% 0.24/0.47                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.24/0.47                                ( ( r1_tarski @
% 0.24/0.47                                    ( k8_relset_1 @
% 0.24/0.47                                      ( u1_struct_0 @ D ) @ 
% 0.24/0.47                                      ( u1_struct_0 @ B ) @ E @ F ) @ 
% 0.24/0.47                                    ( u1_struct_0 @ C ) ) =>
% 0.24/0.47                                  ( ( k8_relset_1 @
% 0.24/0.47                                      ( u1_struct_0 @ D ) @ 
% 0.24/0.47                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.24/0.47                                    ( k8_relset_1 @
% 0.24/0.47                                      ( u1_struct_0 @ C ) @ 
% 0.24/0.47                                      ( u1_struct_0 @ B ) @ 
% 0.24/0.47                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.24/0.47    inference('cnf.neg', [status(esa)], [t76_tmap_1])).
% 0.24/0.47  thf('0', plain,
% 0.24/0.47      (((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.24/0.47         sk_F)
% 0.24/0.47         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.47             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('1', plain,
% 0.24/0.47      ((m1_subset_1 @ sk_E @ 
% 0.24/0.47        (k1_zfmisc_1 @ 
% 0.24/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(redefinition_k8_relset_1, axiom,
% 0.24/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.47       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.24/0.47  thf('2', plain,
% 0.24/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.24/0.47          | ((k8_relset_1 @ X5 @ X6 @ X4 @ X7) = (k10_relat_1 @ X4 @ X7)))),
% 0.24/0.47      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.24/0.47  thf('3', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         ((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.24/0.47           X0) = (k10_relat_1 @ sk_E @ X0))),
% 0.24/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.47  thf('4', plain,
% 0.24/0.47      (((k10_relat_1 @ sk_E @ sk_F)
% 0.24/0.47         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.47             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.24/0.47      inference('demod', [status(thm)], ['0', '3'])).
% 0.24/0.47  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('7', plain,
% 0.24/0.47      ((m1_subset_1 @ sk_E @ 
% 0.24/0.47        (k1_zfmisc_1 @ 
% 0.24/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(d5_tmap_1, axiom,
% 0.24/0.47    (![A:$i]:
% 0.24/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.47       ( ![B:$i]:
% 0.24/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.24/0.47             ( l1_pre_topc @ B ) ) =>
% 0.24/0.47           ( ![C:$i]:
% 0.24/0.47             ( ( m1_pre_topc @ C @ A ) =>
% 0.24/0.47               ( ![D:$i]:
% 0.24/0.47                 ( ( m1_pre_topc @ D @ A ) =>
% 0.24/0.47                   ( ![E:$i]:
% 0.24/0.47                     ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.47                         ( v1_funct_2 @
% 0.24/0.47                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.47                         ( m1_subset_1 @
% 0.24/0.47                           E @ 
% 0.24/0.47                           ( k1_zfmisc_1 @
% 0.24/0.47                             ( k2_zfmisc_1 @
% 0.24/0.47                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.47                       ( ( m1_pre_topc @ D @ C ) =>
% 0.24/0.47                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.24/0.47                           ( k2_partfun1 @
% 0.24/0.47                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.24/0.47                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.47  thf('8', plain,
% 0.24/0.47      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.24/0.47         ((v2_struct_0 @ X24)
% 0.24/0.47          | ~ (v2_pre_topc @ X24)
% 0.24/0.47          | ~ (l1_pre_topc @ X24)
% 0.24/0.47          | ~ (m1_pre_topc @ X25 @ X26)
% 0.24/0.47          | ~ (m1_pre_topc @ X25 @ X27)
% 0.24/0.47          | ((k3_tmap_1 @ X26 @ X24 @ X27 @ X25 @ X28)
% 0.24/0.47              = (k2_partfun1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24) @ 
% 0.24/0.47                 X28 @ (u1_struct_0 @ X25)))
% 0.24/0.47          | ~ (m1_subset_1 @ X28 @ 
% 0.24/0.47               (k1_zfmisc_1 @ 
% 0.24/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))))
% 0.24/0.47          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X24))
% 0.24/0.47          | ~ (v1_funct_1 @ X28)
% 0.24/0.47          | ~ (m1_pre_topc @ X27 @ X26)
% 0.24/0.47          | ~ (l1_pre_topc @ X26)
% 0.24/0.47          | ~ (v2_pre_topc @ X26)
% 0.24/0.47          | (v2_struct_0 @ X26))),
% 0.24/0.47      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.24/0.47  thf('9', plain,
% 0.24/0.47      (![X0 : $i, X1 : $i]:
% 0.24/0.47         ((v2_struct_0 @ X0)
% 0.24/0.47          | ~ (v2_pre_topc @ X0)
% 0.24/0.47          | ~ (l1_pre_topc @ X0)
% 0.24/0.47          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.24/0.47          | ~ (v1_funct_1 @ sk_E)
% 0.24/0.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.24/0.47          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.24/0.47              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.47                 sk_E @ (u1_struct_0 @ X1)))
% 0.24/0.47          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.24/0.47          | ~ (m1_pre_topc @ X1 @ X0)
% 0.24/0.47          | ~ (l1_pre_topc @ sk_B)
% 0.24/0.47          | ~ (v2_pre_topc @ sk_B)
% 0.24/0.47          | (v2_struct_0 @ sk_B))),
% 0.24/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.47  thf('10', plain, ((v1_funct_1 @ sk_E)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('11', plain,
% 0.24/0.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('12', plain,
% 0.24/0.47      ((m1_subset_1 @ sk_E @ 
% 0.24/0.47        (k1_zfmisc_1 @ 
% 0.24/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(redefinition_k2_partfun1, axiom,
% 0.24/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.47     ( ( ( v1_funct_1 @ C ) & 
% 0.24/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.47       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.24/0.47  thf('13', plain,
% 0.24/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.47         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.24/0.47          | ~ (v1_funct_1 @ X8)
% 0.24/0.47          | ((k2_partfun1 @ X9 @ X10 @ X8 @ X11) = (k7_relat_1 @ X8 @ X11)))),
% 0.24/0.47      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.24/0.47  thf('14', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.24/0.47            X0) = (k7_relat_1 @ sk_E @ X0))
% 0.24/0.47          | ~ (v1_funct_1 @ sk_E))),
% 0.24/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.47  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('16', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.24/0.47           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.24/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.24/0.47  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('18', plain, ((v2_pre_topc @ sk_B)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('19', plain,
% 0.24/0.47      (![X0 : $i, X1 : $i]:
% 0.24/0.47         ((v2_struct_0 @ X0)
% 0.24/0.47          | ~ (v2_pre_topc @ X0)
% 0.24/0.47          | ~ (l1_pre_topc @ X0)
% 0.24/0.47          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.24/0.47          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.24/0.47              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.24/0.47          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.24/0.47          | ~ (m1_pre_topc @ X1 @ X0)
% 0.24/0.47          | (v2_struct_0 @ sk_B))),
% 0.24/0.47      inference('demod', [status(thm)], ['9', '10', '11', '16', '17', '18'])).
% 0.24/0.47  thf('20', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         ((v2_struct_0 @ sk_B)
% 0.24/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.24/0.47          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.24/0.47              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.24/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.47          | (v2_struct_0 @ sk_A))),
% 0.24/0.47      inference('sup-', [status(thm)], ['6', '19'])).
% 0.24/0.47  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('23', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         ((v2_struct_0 @ sk_B)
% 0.24/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.24/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.24/0.47          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.24/0.47              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.24/0.47          | (v2_struct_0 @ sk_A))),
% 0.24/0.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.24/0.47  thf('24', plain,
% 0.24/0.47      (((v2_struct_0 @ sk_A)
% 0.24/0.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.24/0.47            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.24/0.47        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.24/0.47        | (v2_struct_0 @ sk_B))),
% 0.24/0.47      inference('sup-', [status(thm)], ['5', '23'])).
% 0.24/0.47  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('26', plain,
% 0.24/0.47      (((v2_struct_0 @ sk_A)
% 0.24/0.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.24/0.47            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.24/0.47        | (v2_struct_0 @ sk_B))),
% 0.24/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.24/0.47  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('28', plain,
% 0.24/0.47      (((v2_struct_0 @ sk_B)
% 0.24/0.47        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.24/0.47            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.24/0.47      inference('clc', [status(thm)], ['26', '27'])).
% 0.24/0.47  thf('29', plain, (~ (v2_struct_0 @ sk_B)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('30', plain,
% 0.24/0.47      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.24/0.47         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.24/0.47      inference('clc', [status(thm)], ['28', '29'])).
% 0.24/0.47  thf(dt_l1_pre_topc, axiom,
% 0.24/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.47  thf('31', plain,
% 0.24/0.47      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.24/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.47  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('33', plain,
% 0.24/0.47      ((m1_subset_1 @ sk_E @ 
% 0.24/0.47        (k1_zfmisc_1 @ 
% 0.24/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(d4_tmap_1, axiom,
% 0.24/0.47    (![A:$i]:
% 0.24/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.47       ( ![B:$i]:
% 0.24/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.24/0.47             ( l1_pre_topc @ B ) ) =>
% 0.24/0.47           ( ![C:$i]:
% 0.24/0.47             ( ( ( v1_funct_1 @ C ) & 
% 0.24/0.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.47                 ( m1_subset_1 @
% 0.24/0.47                   C @ 
% 0.24/0.47                   ( k1_zfmisc_1 @
% 0.24/0.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.47               ( ![D:$i]:
% 0.24/0.47                 ( ( m1_pre_topc @ D @ A ) =>
% 0.24/0.47                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.24/0.47                     ( k2_partfun1 @
% 0.24/0.47                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.24/0.47                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.47  thf('34', plain,
% 0.24/0.47      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.24/0.47         ((v2_struct_0 @ X20)
% 0.24/0.47          | ~ (v2_pre_topc @ X20)
% 0.24/0.47          | ~ (l1_pre_topc @ X20)
% 0.24/0.47          | ~ (m1_pre_topc @ X21 @ X22)
% 0.24/0.47          | ((k2_tmap_1 @ X22 @ X20 @ X23 @ X21)
% 0.24/0.47              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20) @ 
% 0.24/0.47                 X23 @ (u1_struct_0 @ X21)))
% 0.24/0.47          | ~ (m1_subset_1 @ X23 @ 
% 0.24/0.47               (k1_zfmisc_1 @ 
% 0.24/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))))
% 0.24/0.47          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X20))
% 0.24/0.47          | ~ (v1_funct_1 @ X23)
% 0.24/0.47          | ~ (l1_pre_topc @ X22)
% 0.24/0.47          | ~ (v2_pre_topc @ X22)
% 0.24/0.47          | (v2_struct_0 @ X22))),
% 0.24/0.47      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.24/0.47  thf('35', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         ((v2_struct_0 @ sk_D)
% 0.24/0.47          | ~ (v2_pre_topc @ sk_D)
% 0.24/0.47          | ~ (l1_pre_topc @ sk_D)
% 0.24/0.47          | ~ (v1_funct_1 @ sk_E)
% 0.24/0.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.24/0.47          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.24/0.47              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.47                 sk_E @ (u1_struct_0 @ X0)))
% 0.24/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.24/0.47          | ~ (l1_pre_topc @ sk_B)
% 0.24/0.47          | ~ (v2_pre_topc @ sk_B)
% 0.24/0.47          | (v2_struct_0 @ sk_B))),
% 0.24/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.24/0.47  thf('36', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(cc1_pre_topc, axiom,
% 0.24/0.47    (![A:$i]:
% 0.24/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.24/0.47  thf('37', plain,
% 0.24/0.47      (![X15 : $i, X16 : $i]:
% 0.24/0.47         (~ (m1_pre_topc @ X15 @ X16)
% 0.24/0.47          | (v2_pre_topc @ X15)
% 0.24/0.47          | ~ (l1_pre_topc @ X16)
% 0.24/0.47          | ~ (v2_pre_topc @ X16))),
% 0.24/0.47      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.24/0.47  thf('38', plain,
% 0.24/0.47      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.24/0.47      inference('sup-', [status(thm)], ['36', '37'])).
% 0.24/0.47  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('41', plain, ((v2_pre_topc @ sk_D)),
% 0.24/0.47      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.24/0.47  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(dt_m1_pre_topc, axiom,
% 0.24/0.47    (![A:$i]:
% 0.24/0.47     ( ( l1_pre_topc @ A ) =>
% 0.24/0.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.24/0.47  thf('43', plain,
% 0.24/0.47      (![X18 : $i, X19 : $i]:
% 0.24/0.47         (~ (m1_pre_topc @ X18 @ X19)
% 0.24/0.47          | (l1_pre_topc @ X18)
% 0.24/0.47          | ~ (l1_pre_topc @ X19))),
% 0.24/0.47      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.24/0.47  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.24/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.24/0.47  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 0.24/0.47      inference('demod', [status(thm)], ['44', '45'])).
% 0.24/0.47  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('48', plain,
% 0.24/0.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('49', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.24/0.47           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.24/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.24/0.47  thf('50', plain, ((l1_pre_topc @ sk_B)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('51', plain, ((v2_pre_topc @ sk_B)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('52', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         ((v2_struct_0 @ sk_D)
% 0.24/0.47          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.24/0.47              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.24/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.24/0.47          | (v2_struct_0 @ sk_B))),
% 0.24/0.47      inference('demod', [status(thm)],
% 0.24/0.47                ['35', '41', '46', '47', '48', '49', '50', '51'])).
% 0.24/0.47  thf('53', plain,
% 0.24/0.47      (((v2_struct_0 @ sk_B)
% 0.24/0.47        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.24/0.47            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.24/0.47        | (v2_struct_0 @ sk_D))),
% 0.24/0.47      inference('sup-', [status(thm)], ['32', '52'])).
% 0.24/0.47  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('55', plain,
% 0.24/0.47      (((v2_struct_0 @ sk_D)
% 0.24/0.47        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.24/0.47            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.24/0.47      inference('clc', [status(thm)], ['53', '54'])).
% 0.24/0.47  thf('56', plain, (~ (v2_struct_0 @ sk_D)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('57', plain,
% 0.24/0.47      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.24/0.47         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.24/0.47      inference('clc', [status(thm)], ['55', '56'])).
% 0.24/0.47  thf('58', plain,
% 0.24/0.47      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.24/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.47  thf('59', plain,
% 0.24/0.47      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.24/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.47  thf('60', plain,
% 0.24/0.47      ((m1_subset_1 @ sk_E @ 
% 0.24/0.47        (k1_zfmisc_1 @ 
% 0.24/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf(dt_k2_tmap_1, axiom,
% 0.24/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.47     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.24/0.47         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.47         ( m1_subset_1 @
% 0.24/0.47           C @ 
% 0.24/0.47           ( k1_zfmisc_1 @
% 0.24/0.47             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.24/0.47         ( l1_struct_0 @ D ) ) =>
% 0.24/0.47       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.24/0.47         ( v1_funct_2 @
% 0.24/0.47           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.24/0.47           ( u1_struct_0 @ B ) ) & 
% 0.24/0.47         ( m1_subset_1 @
% 0.24/0.47           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.24/0.47           ( k1_zfmisc_1 @
% 0.24/0.47             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.24/0.47  thf('61', plain,
% 0.24/0.47      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.24/0.47         (~ (m1_subset_1 @ X29 @ 
% 0.24/0.47             (k1_zfmisc_1 @ 
% 0.24/0.47              (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))))
% 0.24/0.47          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X31))
% 0.24/0.47          | ~ (v1_funct_1 @ X29)
% 0.24/0.47          | ~ (l1_struct_0 @ X31)
% 0.24/0.47          | ~ (l1_struct_0 @ X30)
% 0.24/0.47          | ~ (l1_struct_0 @ X32)
% 0.24/0.47          | (m1_subset_1 @ (k2_tmap_1 @ X30 @ X31 @ X29 @ X32) @ 
% 0.24/0.47             (k1_zfmisc_1 @ 
% 0.24/0.47              (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X31)))))),
% 0.24/0.47      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.24/0.47  thf('62', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.24/0.47           (k1_zfmisc_1 @ 
% 0.24/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.24/0.47          | ~ (l1_struct_0 @ X0)
% 0.24/0.47          | ~ (l1_struct_0 @ sk_D)
% 0.24/0.47          | ~ (l1_struct_0 @ sk_B)
% 0.24/0.47          | ~ (v1_funct_1 @ sk_E)
% 0.24/0.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.24/0.47      inference('sup-', [status(thm)], ['60', '61'])).
% 0.24/0.47  thf('63', plain, ((v1_funct_1 @ sk_E)),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('64', plain,
% 0.24/0.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.24/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.47  thf('65', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.24/0.47           (k1_zfmisc_1 @ 
% 0.24/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.24/0.47          | ~ (l1_struct_0 @ X0)
% 0.24/0.47          | ~ (l1_struct_0 @ sk_D)
% 0.24/0.47          | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.47      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.24/0.47  thf('66', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         (~ (l1_pre_topc @ sk_D)
% 0.24/0.47          | ~ (l1_struct_0 @ sk_B)
% 0.24/0.47          | ~ (l1_struct_0 @ X0)
% 0.24/0.47          | (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.24/0.47             (k1_zfmisc_1 @ 
% 0.24/0.47              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.24/0.47      inference('sup-', [status(thm)], ['59', '65'])).
% 0.24/0.47  thf('67', plain, ((l1_pre_topc @ sk_D)),
% 0.24/0.47      inference('demod', [status(thm)], ['44', '45'])).
% 0.24/0.47  thf('68', plain,
% 0.24/0.47      (![X0 : $i]:
% 0.24/0.47         (~ (l1_struct_0 @ sk_B)
% 0.24/0.47          | ~ (l1_struct_0 @ X0)
% 0.24/0.47          | (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.24/0.47             (k1_zfmisc_1 @ 
% 0.24/0.47              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.24/0.48      inference('demod', [status(thm)], ['66', '67'])).
% 0.24/0.48  thf('69', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         (~ (l1_pre_topc @ sk_B)
% 0.24/0.48          | (m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.24/0.48             (k1_zfmisc_1 @ 
% 0.24/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.24/0.48          | ~ (l1_struct_0 @ X0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['58', '68'])).
% 0.24/0.48  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('71', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 0.24/0.48           (k1_zfmisc_1 @ 
% 0.24/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.24/0.48          | ~ (l1_struct_0 @ X0))),
% 0.24/0.48      inference('demod', [status(thm)], ['69', '70'])).
% 0.24/0.48  thf('72', plain,
% 0.24/0.48      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 0.24/0.48         (k1_zfmisc_1 @ 
% 0.24/0.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.24/0.48        | ~ (l1_struct_0 @ sk_C))),
% 0.24/0.48      inference('sup+', [status(thm)], ['57', '71'])).
% 0.24/0.48  thf('73', plain,
% 0.24/0.48      ((~ (l1_pre_topc @ sk_C)
% 0.24/0.48        | (m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 0.24/0.48           (k1_zfmisc_1 @ 
% 0.24/0.48            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.24/0.48      inference('sup-', [status(thm)], ['31', '72'])).
% 0.24/0.48  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('75', plain,
% 0.24/0.48      (![X18 : $i, X19 : $i]:
% 0.24/0.48         (~ (m1_pre_topc @ X18 @ X19)
% 0.24/0.48          | (l1_pre_topc @ X18)
% 0.24/0.48          | ~ (l1_pre_topc @ X19))),
% 0.24/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.24/0.48  thf('76', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.24/0.48      inference('sup-', [status(thm)], ['74', '75'])).
% 0.24/0.48  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('78', plain, ((l1_pre_topc @ sk_C)),
% 0.24/0.48      inference('demod', [status(thm)], ['76', '77'])).
% 0.24/0.48  thf('79', plain,
% 0.24/0.48      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 0.24/0.48        (k1_zfmisc_1 @ 
% 0.24/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.48      inference('demod', [status(thm)], ['73', '78'])).
% 0.24/0.48  thf('80', plain,
% 0.24/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.24/0.48          | ((k8_relset_1 @ X5 @ X6 @ X4 @ X7) = (k10_relat_1 @ X4 @ X7)))),
% 0.24/0.48      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.24/0.48  thf('81', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         ((k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.48           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ X0)
% 0.24/0.48           = (k10_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ X0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['79', '80'])).
% 0.24/0.48  thf('82', plain,
% 0.24/0.48      ((r1_tarski @ 
% 0.24/0.48        (k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.24/0.48         sk_F) @ 
% 0.24/0.48        (u1_struct_0 @ sk_C))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('83', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         ((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.24/0.48           X0) = (k10_relat_1 @ sk_E @ X0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.48  thf('84', plain,
% 0.24/0.48      ((r1_tarski @ (k10_relat_1 @ sk_E @ sk_F) @ (u1_struct_0 @ sk_C))),
% 0.24/0.48      inference('demod', [status(thm)], ['82', '83'])).
% 0.24/0.48  thf(t175_funct_2, axiom,
% 0.24/0.48    (![A:$i]:
% 0.24/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.48       ( ![B:$i,C:$i]:
% 0.24/0.48         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.24/0.48           ( ( k10_relat_1 @ A @ C ) =
% 0.24/0.48             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.24/0.48  thf('85', plain,
% 0.24/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.48         (~ (r1_tarski @ (k10_relat_1 @ X12 @ X13) @ X14)
% 0.24/0.48          | ((k10_relat_1 @ X12 @ X13)
% 0.24/0.48              = (k10_relat_1 @ (k7_relat_1 @ X12 @ X14) @ X13))
% 0.24/0.48          | ~ (v1_funct_1 @ X12)
% 0.24/0.48          | ~ (v1_relat_1 @ X12))),
% 0.24/0.48      inference('cnf', [status(esa)], [t175_funct_2])).
% 0.24/0.48  thf('86', plain,
% 0.24/0.48      ((~ (v1_relat_1 @ sk_E)
% 0.24/0.48        | ~ (v1_funct_1 @ sk_E)
% 0.24/0.48        | ((k10_relat_1 @ sk_E @ sk_F)
% 0.24/0.48            = (k10_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F)))),
% 0.24/0.48      inference('sup-', [status(thm)], ['84', '85'])).
% 0.24/0.48  thf('87', plain,
% 0.24/0.48      ((m1_subset_1 @ sk_E @ 
% 0.24/0.48        (k1_zfmisc_1 @ 
% 0.24/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf(cc2_relat_1, axiom,
% 0.24/0.48    (![A:$i]:
% 0.24/0.48     ( ( v1_relat_1 @ A ) =>
% 0.24/0.48       ( ![B:$i]:
% 0.24/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.24/0.48  thf('88', plain,
% 0.24/0.48      (![X0 : $i, X1 : $i]:
% 0.24/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.24/0.48          | (v1_relat_1 @ X0)
% 0.24/0.48          | ~ (v1_relat_1 @ X1))),
% 0.24/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.24/0.48  thf('89', plain,
% 0.24/0.48      ((~ (v1_relat_1 @ 
% 0.24/0.48           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.24/0.48        | (v1_relat_1 @ sk_E))),
% 0.24/0.48      inference('sup-', [status(thm)], ['87', '88'])).
% 0.24/0.48  thf(fc6_relat_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.24/0.48  thf('90', plain,
% 0.24/0.48      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.24/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.48  thf('91', plain, ((v1_relat_1 @ sk_E)),
% 0.24/0.48      inference('demod', [status(thm)], ['89', '90'])).
% 0.24/0.48  thf('92', plain, ((v1_funct_1 @ sk_E)),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('93', plain,
% 0.24/0.48      (((k10_relat_1 @ sk_E @ sk_F)
% 0.24/0.48         = (k10_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.24/0.48      inference('demod', [status(thm)], ['86', '91', '92'])).
% 0.24/0.48  thf('94', plain,
% 0.24/0.48      (((k10_relat_1 @ sk_E @ sk_F) != (k10_relat_1 @ sk_E @ sk_F))),
% 0.24/0.48      inference('demod', [status(thm)], ['4', '30', '81', '93'])).
% 0.24/0.48  thf('95', plain, ($false), inference('simplify', [status(thm)], ['94'])).
% 0.24/0.48  
% 0.24/0.48  % SZS output end Refutation
% 0.24/0.48  
% 0.24/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
