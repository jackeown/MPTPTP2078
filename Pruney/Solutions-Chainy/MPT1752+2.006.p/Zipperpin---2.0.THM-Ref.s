%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tNSavPBaGc

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:50 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 185 expanded)
%              Number of leaves         :   41 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  980 (4147 expanded)
%              Number of equality atoms :   26 (  73 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t62_tmap_1,conjecture,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ ( u1_struct_0 @ C ) )
                       => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E )
                          = ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) )).

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
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ( ( r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ ( u1_struct_0 @ C ) )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E )
                            = ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tmap_1])).

thf('0',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_E )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k8_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k10_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k10_relat_1 @ sk_D @ sk_E )
 != ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_E ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('7',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ( ( k2_tmap_1 @ X37 @ X35 @ X38 @ X36 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) @ X38 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( ( k2_partfun1 @ X29 @ X30 @ X28 @ X31 )
        = ( k7_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12','17','18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(cc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v5_relat_1 @ C @ A ) ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v5_relat_1 @ X5 @ X7 )
      | ~ ( v5_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc6_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( v5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('50',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X27 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k8_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k10_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('62',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(t175_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf('63',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ X34 )
      | ( ( k10_relat_1 @ X32 @ X33 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X32 @ X34 ) @ X33 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t175_funct_2])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k10_relat_1 @ sk_D @ sk_E )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['40','41'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k10_relat_1 @ sk_D @ sk_E )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ( k10_relat_1 @ sk_D @ sk_E )
 != ( k10_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['4','25','59','67'])).

thf('69',plain,(
    $false ),
    inference(simplify,[status(thm)],['68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tNSavPBaGc
% 0.15/0.36  % Computer   : n009.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 13:26:56 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 153 iterations in 0.097s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.58  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.40/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.40/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.40/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.58  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.40/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(t62_tmap_1, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.58             ( l1_pre_topc @ B ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.40/0.58               ( ![D:$i]:
% 0.40/0.58                 ( ( ( v1_funct_1 @ D ) & 
% 0.40/0.58                     ( v1_funct_2 @
% 0.40/0.58                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.58                     ( m1_subset_1 @
% 0.40/0.58                       D @ 
% 0.40/0.58                       ( k1_zfmisc_1 @
% 0.40/0.58                         ( k2_zfmisc_1 @
% 0.40/0.58                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.58                   ( ![E:$i]:
% 0.40/0.58                     ( ( m1_subset_1 @
% 0.40/0.58                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.40/0.58                       ( ( r1_tarski @
% 0.40/0.58                           ( k8_relset_1 @
% 0.40/0.58                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) @ 
% 0.40/0.58                           ( u1_struct_0 @ C ) ) =>
% 0.40/0.58                         ( ( k8_relset_1 @
% 0.40/0.58                             ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ D @ E ) =
% 0.40/0.58                           ( k8_relset_1 @
% 0.40/0.58                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.58                             ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.40/0.58            ( l1_pre_topc @ A ) ) =>
% 0.40/0.58          ( ![B:$i]:
% 0.40/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.58                ( l1_pre_topc @ B ) ) =>
% 0.40/0.58              ( ![C:$i]:
% 0.40/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.40/0.58                  ( ![D:$i]:
% 0.40/0.58                    ( ( ( v1_funct_1 @ D ) & 
% 0.40/0.58                        ( v1_funct_2 @
% 0.40/0.58                          D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.58                        ( m1_subset_1 @
% 0.40/0.58                          D @ 
% 0.40/0.58                          ( k1_zfmisc_1 @
% 0.40/0.58                            ( k2_zfmisc_1 @
% 0.40/0.58                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.58                      ( ![E:$i]:
% 0.40/0.58                        ( ( m1_subset_1 @
% 0.40/0.58                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.40/0.58                          ( ( r1_tarski @
% 0.40/0.58                              ( k8_relset_1 @
% 0.40/0.58                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.58                                D @ E ) @ 
% 0.40/0.58                              ( u1_struct_0 @ C ) ) =>
% 0.40/0.58                            ( ( k8_relset_1 @
% 0.40/0.58                                ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.58                                D @ E ) =
% 0.40/0.58                              ( k8_relset_1 @
% 0.40/0.58                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.40/0.58                                ( k2_tmap_1 @ A @ B @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t62_tmap_1])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.40/0.58         sk_E)
% 0.40/0.58         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.58             (k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_E))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(redefinition_k8_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.40/0.58          | ((k8_relset_1 @ X22 @ X23 @ X21 @ X24) = (k10_relat_1 @ X21 @ X24)))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.40/0.58           X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (((k10_relat_1 @ sk_D @ sk_E)
% 0.40/0.58         != (k8_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.58             (k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_E))),
% 0.40/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.40/0.58  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d4_tmap_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.40/0.58             ( l1_pre_topc @ B ) ) =>
% 0.40/0.58           ( ![C:$i]:
% 0.40/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.40/0.58                 ( m1_subset_1 @
% 0.40/0.58                   C @ 
% 0.40/0.58                   ( k1_zfmisc_1 @
% 0.40/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.40/0.58               ( ![D:$i]:
% 0.40/0.58                 ( ( m1_pre_topc @ D @ A ) =>
% 0.40/0.58                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.40/0.58                     ( k2_partfun1 @
% 0.40/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.40/0.58                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.40/0.58         ((v2_struct_0 @ X35)
% 0.40/0.58          | ~ (v2_pre_topc @ X35)
% 0.40/0.58          | ~ (l1_pre_topc @ X35)
% 0.40/0.58          | ~ (m1_pre_topc @ X36 @ X37)
% 0.40/0.58          | ((k2_tmap_1 @ X37 @ X35 @ X38 @ X36)
% 0.40/0.58              = (k2_partfun1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35) @ 
% 0.40/0.58                 X38 @ (u1_struct_0 @ X36)))
% 0.40/0.58          | ~ (m1_subset_1 @ X38 @ 
% 0.40/0.58               (k1_zfmisc_1 @ 
% 0.40/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))))
% 0.40/0.58          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))
% 0.40/0.58          | ~ (v1_funct_1 @ X38)
% 0.40/0.58          | ~ (l1_pre_topc @ X37)
% 0.40/0.58          | ~ (v2_pre_topc @ X37)
% 0.40/0.58          | (v2_struct_0 @ X37))),
% 0.40/0.58      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v2_struct_0 @ sk_A)
% 0.40/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.40/0.58          | ~ (v1_funct_1 @ sk_D)
% 0.40/0.58          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.40/0.58          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.40/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.58                 sk_D @ (u1_struct_0 @ X0)))
% 0.40/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.40/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.40/0.58          | (v2_struct_0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(redefinition_k2_partfun1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( ( v1_funct_1 @ C ) & 
% 0.40/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.58       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.40/0.58          | ~ (v1_funct_1 @ X28)
% 0.40/0.58          | ((k2_partfun1 @ X29 @ X30 @ X28 @ X31) = (k7_relat_1 @ X28 @ X31)))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.40/0.58            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.40/0.58          | ~ (v1_funct_1 @ sk_D))),
% 0.40/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.40/0.58           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((v2_struct_0 @ sk_A)
% 0.40/0.58          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ X0)
% 0.40/0.58              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.40/0.58          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.40/0.58          | (v2_struct_0 @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)],
% 0.40/0.58                ['8', '9', '10', '11', '12', '17', '18', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (((v2_struct_0 @ sk_B)
% 0.40/0.58        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.40/0.58            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.40/0.58        | (v2_struct_0 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '20'])).
% 0.40/0.58  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (((v2_struct_0 @ sk_A)
% 0.40/0.58        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.40/0.58            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.40/0.58      inference('clc', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (((k2_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C)
% 0.40/0.58         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.40/0.58      inference('clc', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf(dt_k7_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X10) | (v1_relat_1 @ (k7_relat_1 @ X10 @ X11)))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc2_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.58         ((v5_relat_1 @ X18 @ X20)
% 0.40/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.58  thf('30', plain, ((v5_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf(t88_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i]:
% 0.40/0.58         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 0.40/0.58      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.40/0.58  thf(t3_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X0 : $i, X2 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf(cc6_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v5_relat_1 @ C @ A ) ) ) ))).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.40/0.58          | (v5_relat_1 @ X5 @ X7)
% 0.40/0.58          | ~ (v5_relat_1 @ X6 @ X7)
% 0.40/0.58          | ~ (v1_relat_1 @ X6))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc6_relat_1])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v5_relat_1 @ X0 @ X2)
% 0.40/0.58          | (v5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2))),
% 0.40/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         ((v5_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2)
% 0.40/0.58          | ~ (v5_relat_1 @ X0 @ X2)
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('simplify', [status(thm)], ['35'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ sk_D)
% 0.40/0.58          | (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['30', '36'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D @ 
% 0.40/0.58        (k1_zfmisc_1 @ 
% 0.40/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc2_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.40/0.58          | (v1_relat_1 @ X3)
% 0.40/0.58          | ~ (v1_relat_1 @ X4))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ 
% 0.40/0.58           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.40/0.58        | (v1_relat_1 @ sk_D))),
% 0.40/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.40/0.58  thf(fc6_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.40/0.58  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ (u1_struct_0 @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['37', '42'])).
% 0.40/0.58  thf(d19_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i]:
% 0.40/0.58         (~ (v5_relat_1 @ X8 @ X9)
% 0.40/0.58          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.40/0.58          | ~ (v1_relat_1 @ X8))),
% 0.40/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.40/0.58          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.40/0.58             (u1_struct_0 @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ sk_D)
% 0.40/0.58          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.40/0.58             (u1_struct_0 @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['27', '45'])).
% 0.40/0.58  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.40/0.58          (u1_struct_0 @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.40/0.58  thf(t87_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.40/0.58  thf('49', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i]:
% 0.40/0.58         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)) @ X15)
% 0.40/0.58          | ~ (v1_relat_1 @ X14))),
% 0.40/0.58      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.40/0.58  thf(t11_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ C ) =>
% 0.40/0.58       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.40/0.58           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.40/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.58         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.40/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X25) @ X27)
% 0.40/0.58          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.40/0.58          | ~ (v1_relat_1 @ X25))),
% 0.40/0.58      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X1)
% 0.40/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.40/0.58          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.40/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.40/0.58          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.40/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.40/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.40/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.40/0.58          | ~ (v1_relat_1 @ sk_D))),
% 0.40/0.58      inference('sup-', [status(thm)], ['48', '51'])).
% 0.40/0.58  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.40/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))
% 0.40/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ sk_D)
% 0.40/0.58          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.40/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B)))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['26', '54'])).
% 0.40/0.58  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.58  thf('57', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.40/0.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B))))),
% 0.40/0.58      inference('demod', [status(thm)], ['55', '56'])).
% 0.40/0.58  thf('58', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.40/0.58          | ((k8_relset_1 @ X22 @ X23 @ X21 @ X24) = (k10_relat_1 @ X21 @ X24)))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.40/0.58  thf('59', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k8_relset_1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.40/0.58           (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.40/0.58           = (k10_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      ((r1_tarski @ 
% 0.40/0.58        (k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.40/0.58         sk_E) @ 
% 0.40/0.58        (u1_struct_0 @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_D @ 
% 0.40/0.58           X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      ((r1_tarski @ (k10_relat_1 @ sk_D @ sk_E) @ (u1_struct_0 @ sk_C))),
% 0.40/0.58      inference('demod', [status(thm)], ['60', '61'])).
% 0.40/0.58  thf(t175_funct_2, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.58       ( ![B:$i,C:$i]:
% 0.40/0.58         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.40/0.58           ( ( k10_relat_1 @ A @ C ) =
% 0.40/0.58             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.40/0.58  thf('63', plain,
% 0.40/0.58      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.40/0.58         (~ (r1_tarski @ (k10_relat_1 @ X32 @ X33) @ X34)
% 0.40/0.58          | ((k10_relat_1 @ X32 @ X33)
% 0.40/0.58              = (k10_relat_1 @ (k7_relat_1 @ X32 @ X34) @ X33))
% 0.40/0.58          | ~ (v1_funct_1 @ X32)
% 0.40/0.58          | ~ (v1_relat_1 @ X32))),
% 0.40/0.58      inference('cnf', [status(esa)], [t175_funct_2])).
% 0.40/0.58  thf('64', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_D)
% 0.40/0.58        | ~ (v1_funct_1 @ sk_D)
% 0.40/0.58        | ((k10_relat_1 @ sk_D @ sk_E)
% 0.40/0.58            = (k10_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['62', '63'])).
% 0.40/0.58  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 0.40/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.58  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('67', plain,
% 0.40/0.58      (((k10_relat_1 @ sk_D @ sk_E)
% 0.40/0.58         = (k10_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.40/0.58      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.40/0.58  thf('68', plain,
% 0.40/0.58      (((k10_relat_1 @ sk_D @ sk_E) != (k10_relat_1 @ sk_D @ sk_E))),
% 0.40/0.58      inference('demod', [status(thm)], ['4', '25', '59', '67'])).
% 0.40/0.58  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
