%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VKuLyaIBBE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 160 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          : 1093 (5706 expanded)
%              Number of equality atoms :   30 (  93 expanded)
%              Maximal formula depth    :   24 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( ( k8_relset_1 @ X4 @ X5 @ X3 @ X6 )
        = ( k10_relat_1 @ X3 @ X6 ) ) ) ),
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

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X20 @ X22 @ X21 @ X19 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X22 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( ( k8_relset_1 @ X4 @ X5 @ X3 @ X6 )
        = ( k10_relat_1 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      = ( k10_relat_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k10_relat_1 @ sk_E @ sk_F )
 != ( k10_relat_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(demod,[status(thm)],['4','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X17 )
      | ( ( k3_tmap_1 @ X16 @ X14 @ X17 @ X15 @ X18 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X14 ) @ X18 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('31',plain,(
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
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ( ( k2_partfun1 @ X8 @ X9 @ X7 @ X10 )
        = ( k7_relat_1 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
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
    inference(demod,[status(thm)],['31','32','33','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('55',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_E @ sk_F ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t175_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf('56',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X11 @ X12 ) @ X13 )
      | ( ( k10_relat_1 @ X11 @ X12 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X11 @ X13 ) @ X12 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t175_funct_2])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( ( k10_relat_1 @ sk_E @ sk_F )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k10_relat_1 @ sk_E @ sk_F )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,(
    ( k10_relat_1 @ sk_E @ sk_F )
 != ( k10_relat_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['26','52','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VKuLyaIBBE
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:53:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 41 iterations in 0.032s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.53  thf(t76_tmap_1, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.53                   ( ![E:$i]:
% 0.22/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.53                         ( v1_funct_2 @
% 0.22/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                         ( m1_subset_1 @
% 0.22/0.53                           E @ 
% 0.22/0.53                           ( k1_zfmisc_1 @
% 0.22/0.53                             ( k2_zfmisc_1 @
% 0.22/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53                       ( ( m1_pre_topc @ C @ D ) =>
% 0.22/0.53                         ( ![F:$i]:
% 0.22/0.53                           ( ( m1_subset_1 @
% 0.22/0.53                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.53                             ( ( r1_tarski @
% 0.22/0.53                                 ( k8_relset_1 @
% 0.22/0.53                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.22/0.53                                   E @ F ) @ 
% 0.22/0.53                                 ( u1_struct_0 @ C ) ) =>
% 0.22/0.53                               ( ( k8_relset_1 @
% 0.22/0.53                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.22/0.53                                   E @ F ) =
% 0.22/0.53                                 ( k8_relset_1 @
% 0.22/0.53                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.22/0.53                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.53            ( l1_pre_topc @ A ) ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53                ( l1_pre_topc @ B ) ) =>
% 0.22/0.53              ( ![C:$i]:
% 0.22/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.53                  ( ![D:$i]:
% 0.22/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.53                      ( ![E:$i]:
% 0.22/0.53                        ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.53                            ( v1_funct_2 @
% 0.22/0.53                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                            ( m1_subset_1 @
% 0.22/0.53                              E @ 
% 0.22/0.53                              ( k1_zfmisc_1 @
% 0.22/0.53                                ( k2_zfmisc_1 @
% 0.22/0.53                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53                          ( ( m1_pre_topc @ C @ D ) =>
% 0.22/0.53                            ( ![F:$i]:
% 0.22/0.53                              ( ( m1_subset_1 @
% 0.22/0.53                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.53                                ( ( r1_tarski @
% 0.22/0.53                                    ( k8_relset_1 @
% 0.22/0.53                                      ( u1_struct_0 @ D ) @ 
% 0.22/0.53                                      ( u1_struct_0 @ B ) @ E @ F ) @ 
% 0.22/0.53                                    ( u1_struct_0 @ C ) ) =>
% 0.22/0.53                                  ( ( k8_relset_1 @
% 0.22/0.53                                      ( u1_struct_0 @ D ) @ 
% 0.22/0.53                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.22/0.53                                    ( k8_relset_1 @
% 0.22/0.53                                      ( u1_struct_0 @ C ) @ 
% 0.22/0.53                                      ( u1_struct_0 @ B ) @ 
% 0.22/0.53                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t76_tmap_1])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.22/0.53         sk_F)
% 0.22/0.53         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.22/0.53          | ((k8_relset_1 @ X4 @ X5 @ X3 @ X6) = (k10_relat_1 @ X3 @ X6)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.22/0.53           X0) = (k10_relat_1 @ sk_E @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_E @ sk_F)
% 0.22/0.53         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.22/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.53  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(dt_k3_tmap_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.53         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.22/0.53         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.22/0.53         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.22/0.53         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53         ( m1_subset_1 @
% 0.22/0.53           E @ 
% 0.22/0.53           ( k1_zfmisc_1 @
% 0.22/0.53             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.22/0.53         ( v1_funct_2 @
% 0.22/0.53           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.22/0.53           ( u1_struct_0 @ B ) ) & 
% 0.22/0.53         ( m1_subset_1 @
% 0.22/0.53           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.22/0.53           ( k1_zfmisc_1 @
% 0.22/0.53             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.53         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.53          | ~ (m1_pre_topc @ X21 @ X20)
% 0.22/0.53          | ~ (l1_pre_topc @ X22)
% 0.22/0.53          | ~ (v2_pre_topc @ X22)
% 0.22/0.53          | (v2_struct_0 @ X22)
% 0.22/0.53          | ~ (l1_pre_topc @ X20)
% 0.22/0.53          | ~ (v2_pre_topc @ X20)
% 0.22/0.53          | (v2_struct_0 @ X20)
% 0.22/0.53          | ~ (v1_funct_1 @ X23)
% 0.22/0.53          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.22/0.53          | ~ (m1_subset_1 @ X23 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))))
% 0.22/0.53          | (m1_subset_1 @ (k3_tmap_1 @ X20 @ X22 @ X21 @ X19 @ X23) @ 
% 0.22/0.53             (k1_zfmisc_1 @ 
% 0.22/0.53              (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X22)))))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 0.22/0.53           (k1_zfmisc_1 @ 
% 0.22/0.53            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.22/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.53          | (v2_struct_0 @ X1)
% 0.22/0.53          | ~ (v2_pre_topc @ X1)
% 0.22/0.53          | ~ (l1_pre_topc @ X1)
% 0.22/0.53          | (v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 0.22/0.53           (k1_zfmisc_1 @ 
% 0.22/0.53            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.22/0.53          | (v2_struct_0 @ X1)
% 0.22/0.53          | ~ (v2_pre_topc @ X1)
% 0.22/0.53          | ~ (l1_pre_topc @ X1)
% 0.22/0.53          | (v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.22/0.53      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.53          | (v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53          | (v2_struct_0 @ sk_A)
% 0.22/0.53          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 0.22/0.53             (k1_zfmisc_1 @ 
% 0.22/0.53              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['6', '14'])).
% 0.22/0.53  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.53          | (v2_struct_0 @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ sk_A)
% 0.22/0.53          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 0.22/0.53             (k1_zfmisc_1 @ 
% 0.22/0.53              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.22/0.53      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 0.22/0.53         (k1_zfmisc_1 @ 
% 0.22/0.53          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.22/0.53        | (v2_struct_0 @ sk_A)
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['5', '18'])).
% 0.22/0.53  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_B)
% 0.22/0.53        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 0.22/0.53           (k1_zfmisc_1 @ 
% 0.22/0.53            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.22/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.53  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('clc', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.22/0.53          | ((k8_relset_1 @ X4 @ X5 @ X3 @ X6) = (k10_relat_1 @ X3 @ X6)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 0.22/0.53           = (k10_relat_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_E @ sk_F)
% 0.22/0.53         != (k10_relat_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 0.22/0.53             sk_F))),
% 0.22/0.53      inference('demod', [status(thm)], ['4', '25'])).
% 0.22/0.53  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(d5_tmap_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.53                   ( ![E:$i]:
% 0.22/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.53                         ( v1_funct_2 @
% 0.22/0.53                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                         ( m1_subset_1 @
% 0.22/0.53                           E @ 
% 0.22/0.53                           ( k1_zfmisc_1 @
% 0.22/0.53                             ( k2_zfmisc_1 @
% 0.22/0.53                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53                       ( ( m1_pre_topc @ D @ C ) =>
% 0.22/0.53                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.53                           ( k2_partfun1 @
% 0.22/0.53                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.22/0.53                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X14)
% 0.22/0.53          | ~ (v2_pre_topc @ X14)
% 0.22/0.53          | ~ (l1_pre_topc @ X14)
% 0.22/0.53          | ~ (m1_pre_topc @ X15 @ X16)
% 0.22/0.53          | ~ (m1_pre_topc @ X15 @ X17)
% 0.22/0.53          | ((k3_tmap_1 @ X16 @ X14 @ X17 @ X15 @ X18)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X14) @ 
% 0.22/0.53                 X18 @ (u1_struct_0 @ X15)))
% 0.22/0.53          | ~ (m1_subset_1 @ X18 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X14))))
% 0.22/0.53          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X14))
% 0.22/0.53          | ~ (v1_funct_1 @ X18)
% 0.22/0.53          | ~ (m1_pre_topc @ X17 @ X16)
% 0.22/0.53          | ~ (l1_pre_topc @ X16)
% 0.22/0.53          | ~ (v2_pre_topc @ X16)
% 0.22/0.53          | (v2_struct_0 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X0)
% 0.22/0.53          | ~ (v2_pre_topc @ X0)
% 0.22/0.53          | ~ (l1_pre_topc @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.53          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.22/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.53                 sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.53  thf('32', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k2_partfun1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.53       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.22/0.53          | ~ (v1_funct_1 @ X7)
% 0.22/0.53          | ((k2_partfun1 @ X8 @ X9 @ X7 @ X10) = (k7_relat_1 @ X7 @ X10)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.22/0.53            X0) = (k7_relat_1 @ sk_E @ X0))
% 0.22/0.53          | ~ (v1_funct_1 @ sk_E))),
% 0.22/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.53  thf('37', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.22/0.53           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.53  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X0)
% 0.22/0.53          | ~ (v2_pre_topc @ X0)
% 0.22/0.53          | ~ (l1_pre_topc @ X0)
% 0.22/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.53          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.22/0.53              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.53          | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['31', '32', '33', '38', '39', '40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.22/0.53              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53          | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['28', '41'])).
% 0.22/0.53  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_B)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.53          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.53          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.22/0.53              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.53          | (v2_struct_0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.22/0.53            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.22/0.53        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['27', '45'])).
% 0.22/0.53  thf('47', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_A)
% 0.22/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.22/0.53            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.22/0.53        | (v2_struct_0 @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      (((v2_struct_0 @ sk_B)
% 0.22/0.53        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.22/0.53            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.22/0.53      inference('clc', [status(thm)], ['48', '49'])).
% 0.22/0.53  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('52', plain,
% 0.22/0.53      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.22/0.53         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.22/0.53      inference('clc', [status(thm)], ['50', '51'])).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      ((r1_tarski @ 
% 0.22/0.53        (k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.22/0.53         sk_F) @ 
% 0.22/0.53        (u1_struct_0 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k8_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.22/0.53           X0) = (k10_relat_1 @ sk_E @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      ((r1_tarski @ (k10_relat_1 @ sk_E @ sk_F) @ (u1_struct_0 @ sk_C))),
% 0.22/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.22/0.53  thf(t175_funct_2, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.53       ( ![B:$i,C:$i]:
% 0.22/0.53         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.22/0.53           ( ( k10_relat_1 @ A @ C ) =
% 0.22/0.53             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.22/0.53  thf('56', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.53         (~ (r1_tarski @ (k10_relat_1 @ X11 @ X12) @ X13)
% 0.22/0.53          | ((k10_relat_1 @ X11 @ X12)
% 0.22/0.53              = (k10_relat_1 @ (k7_relat_1 @ X11 @ X13) @ X12))
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [t175_funct_2])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_E)
% 0.22/0.53        | ~ (v1_funct_1 @ sk_E)
% 0.22/0.53        | ((k10_relat_1 @ sk_E @ sk_F)
% 0.22/0.53            = (k10_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc1_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( v1_relat_1 @ C ) ))).
% 0.22/0.53  thf('59', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((v1_relat_1 @ X0)
% 0.22/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.53  thf('60', plain, ((v1_relat_1 @ sk_E)),
% 0.22/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.53  thf('61', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('62', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_E @ sk_F)
% 0.22/0.53         = (k10_relat_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.22/0.53      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.22/0.53  thf('63', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_E @ sk_F) != (k10_relat_1 @ sk_E @ sk_F))),
% 0.22/0.53      inference('demod', [status(thm)], ['26', '52', '62'])).
% 0.22/0.53  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
