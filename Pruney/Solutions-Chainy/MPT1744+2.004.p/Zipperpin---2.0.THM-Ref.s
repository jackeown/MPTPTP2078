%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G7ZcC0M4ps

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 370 expanded)
%              Number of leaves         :   43 ( 127 expanded)
%              Depth                    :   22
%              Number of atoms          : 1829 (15797 expanded)
%              Number of equality atoms :   25 (  46 expanded)
%              Maximal formula depth    :   30 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t53_tmap_1,conjecture,(
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
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ( ( ( v5_pre_topc @ D @ C @ B )
                              & ( r1_tmap_1 @ B @ A @ E @ F ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( r2_hidden @ G @ ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ F ) ) )
                                 => ( r1_tmap_1 @ C @ A @ ( k1_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) @ G ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( ( v5_pre_topc @ D @ C @ B )
                                & ( r1_tmap_1 @ B @ A @ E @ F ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( r2_hidden @ G @ ( k8_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ F ) ) )
                                   => ( r1_tmap_1 @ C @ A @ ( k1_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) @ G ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( r2_hidden @ X31 @ ( k1_connsp_2 @ X32 @ X31 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ( r2_hidden @ sk_G @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_G @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ sk_G @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ X24 )
      | ( ( k3_funct_2 @ X24 @ X25 @ X23 @ X26 )
        = ( k1_funct_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ X0 )
        = ( k1_funct_1 @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ X0 )
        = ( k1_funct_1 @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G )
      = ( k1_funct_1 @ sk_D_2 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( r2_hidden @ X31 @ ( k1_connsp_2 @ X32 @ X31 ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t30_connsp_2])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( r2_hidden @ sk_F @ ( k1_connsp_2 @ sk_B @ sk_F ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_F @ ( k1_connsp_2 @ sk_B @ sk_F ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ sk_F @ ( k1_connsp_2 @ sk_B @ sk_F ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( ( k6_domain_1 @ X27 @ X28 )
        = ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F )
      = ( k1_tarski @ sk_F ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_G @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r2_hidden @ sk_G @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k1_tarski @ sk_F ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k8_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k10_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_G @ ( k10_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_F ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k10_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X17 ) @ X14 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k10_relat_1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X17 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_G ) @ ( k1_tarski @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_G ) @ ( k1_tarski @ sk_F ) ) ),
    inference(demod,[status(thm)],['36','37','42'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('45',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_G )
      = sk_F ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_B @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_B @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_B @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('55',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_B @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D_2 @ sk_G )
        = sk_F )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_B @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['46','56'])).

thf('58',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_G )
    = sk_F ),
    inference('sup-',[status(thm)],['24','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G )
      = sk_F ) ),
    inference(demod,[status(thm)],['16','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G )
      = sk_F ) ),
    inference(demod,[status(thm)],['16','58'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_tmap_1,axiom,(
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
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                             => ( ( ( G
                                    = ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ D @ F ) )
                                  & ( r1_tmap_1 @ B @ C @ D @ F )
                                  & ( r1_tmap_1 @ C @ A @ E @ G ) )
                               => ( r1_tmap_1 @ B @ A @ ( k1_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ E ) @ F ) ) ) ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r1_tmap_1 @ X37 @ X39 @ X38 @ X40 )
      | ( r1_tmap_1 @ X37 @ X41 @ ( k1_partfun1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) @ X38 @ X42 ) @ X40 )
      | ( X43
       != ( k3_funct_2 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ X38 @ X40 ) )
      | ~ ( r1_tmap_1 @ X39 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t52_tmap_1])).

thf('63',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ X38 @ X40 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( r1_tmap_1 @ X39 @ X41 @ X42 @ ( k3_funct_2 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ X38 @ X40 ) )
      | ( r1_tmap_1 @ X37 @ X41 @ ( k1_partfun1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X41 ) @ X38 @ X42 ) @ X40 )
      | ~ ( r1_tmap_1 @ X37 @ X39 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ X1 @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_E ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_E @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ X1 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','69','70'])).

thf('72',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G ) @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,(
    r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ( ( v5_pre_topc @ C @ B @ A )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v5_pre_topc @ X34 @ X33 @ X35 )
      | ( r1_tmap_1 @ X33 @ X35 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0 )
      | ~ ( v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82','83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G ) @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['72','73','90','91','92','93','94','95','96'])).

thf('98',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['59','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['0','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G7ZcC0M4ps
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 171 iterations in 0.089s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.55  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.55  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.55  thf(t53_tmap_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55             ( l1_pre_topc @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.20/0.55                 ( l1_pre_topc @ C ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.55                     ( v1_funct_2 @
% 0.20/0.55                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                     ( m1_subset_1 @
% 0.20/0.55                       D @ 
% 0.20/0.55                       ( k1_zfmisc_1 @
% 0.20/0.55                         ( k2_zfmisc_1 @
% 0.20/0.55                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                         ( v1_funct_2 @
% 0.20/0.55                           E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ 
% 0.20/0.55                           ( k1_zfmisc_1 @
% 0.20/0.55                             ( k2_zfmisc_1 @
% 0.20/0.55                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.55                       ( ![F:$i]:
% 0.20/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                           ( ( ( v5_pre_topc @ D @ C @ B ) & 
% 0.20/0.55                               ( r1_tmap_1 @ B @ A @ E @ F ) ) =>
% 0.20/0.55                             ( ![G:$i]:
% 0.20/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                                 ( ( r2_hidden @
% 0.20/0.55                                     G @ 
% 0.20/0.55                                     ( k8_relset_1 @
% 0.20/0.55                                       ( u1_struct_0 @ C ) @ 
% 0.20/0.55                                       ( u1_struct_0 @ B ) @ D @ 
% 0.20/0.55                                       ( k6_domain_1 @ ( u1_struct_0 @ B ) @ F ) ) ) =>
% 0.20/0.55                                   ( r1_tmap_1 @
% 0.20/0.55                                     C @ A @ 
% 0.20/0.55                                     ( k1_partfun1 @
% 0.20/0.55                                       ( u1_struct_0 @ C ) @ 
% 0.20/0.55                                       ( u1_struct_0 @ B ) @ 
% 0.20/0.55                                       ( u1_struct_0 @ B ) @ 
% 0.20/0.55                                       ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.20/0.55                                     G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55            ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55                ( l1_pre_topc @ B ) ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.20/0.55                    ( l1_pre_topc @ C ) ) =>
% 0.20/0.55                  ( ![D:$i]:
% 0.20/0.55                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.55                        ( v1_funct_2 @
% 0.20/0.55                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                        ( m1_subset_1 @
% 0.20/0.55                          D @ 
% 0.20/0.55                          ( k1_zfmisc_1 @
% 0.20/0.55                            ( k2_zfmisc_1 @
% 0.20/0.55                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                      ( ![E:$i]:
% 0.20/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                            ( v1_funct_2 @
% 0.20/0.55                              E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.55                            ( m1_subset_1 @
% 0.20/0.55                              E @ 
% 0.20/0.55                              ( k1_zfmisc_1 @
% 0.20/0.55                                ( k2_zfmisc_1 @
% 0.20/0.55                                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.55                          ( ![F:$i]:
% 0.20/0.55                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                              ( ( ( v5_pre_topc @ D @ C @ B ) & 
% 0.20/0.55                                  ( r1_tmap_1 @ B @ A @ E @ F ) ) =>
% 0.20/0.55                                ( ![G:$i]:
% 0.20/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                                    ( ( r2_hidden @
% 0.20/0.55                                        G @ 
% 0.20/0.55                                        ( k8_relset_1 @
% 0.20/0.55                                          ( u1_struct_0 @ C ) @ 
% 0.20/0.55                                          ( u1_struct_0 @ B ) @ D @ 
% 0.20/0.55                                          ( k6_domain_1 @
% 0.20/0.55                                            ( u1_struct_0 @ B ) @ F ) ) ) =>
% 0.20/0.55                                      ( r1_tmap_1 @
% 0.20/0.55                                        C @ A @ 
% 0.20/0.55                                        ( k1_partfun1 @
% 0.20/0.55                                          ( u1_struct_0 @ C ) @ 
% 0.20/0.55                                          ( u1_struct_0 @ B ) @ 
% 0.20/0.55                                          ( u1_struct_0 @ B ) @ 
% 0.20/0.55                                          ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.20/0.55                                        G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t53_tmap_1])).
% 0.20/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t30_connsp_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X31 : $i, X32 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.20/0.55          | (r2_hidden @ X31 @ (k1_connsp_2 @ X32 @ X31))
% 0.20/0.55          | ~ (l1_pre_topc @ X32)
% 0.20/0.55          | ~ (v2_pre_topc @ X32)
% 0.20/0.55          | (v2_struct_0 @ X32))),
% 0.20/0.55      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_C_1)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_C_1)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_C_1)
% 0.20/0.55        | (r2_hidden @ sk_G @ (k1_connsp_2 @ sk_C_1 @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf('4', plain, ((v2_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('5', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_C_1)
% 0.20/0.55        | (r2_hidden @ sk_G @ (k1_connsp_2 @ sk_C_1 @ sk_G)))),
% 0.20/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.55  thf('7', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('8', plain, ((r2_hidden @ sk_G @ (k1_connsp_2 @ sk_C_1 @ sk_G))),
% 0.20/0.55      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('9', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.55         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.55       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.20/0.55          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.20/0.55          | ~ (v1_funct_1 @ X23)
% 0.20/0.55          | (v1_xboole_0 @ X24)
% 0.20/0.55          | ~ (m1_subset_1 @ X26 @ X24)
% 0.20/0.55          | ((k3_funct_2 @ X24 @ X25 @ X23 @ X26) = (k1_funct_1 @ X23 @ X26)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            sk_D_2 @ X0) = (k1_funct_1 @ sk_D_2 @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55               (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf('13', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            sk_D_2 @ X0) = (k1_funct_1 @ sk_D_2 @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            sk_D_2 @ sk_G) = (k1_funct_1 @ sk_D_2 @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.55  thf('17', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X31 : $i, X32 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.20/0.55          | (r2_hidden @ X31 @ (k1_connsp_2 @ X32 @ X31))
% 0.20/0.55          | ~ (l1_pre_topc @ X32)
% 0.20/0.55          | ~ (v2_pre_topc @ X32)
% 0.20/0.55          | (v2_struct_0 @ X32))),
% 0.20/0.55      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.55        | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_B @ sk_F)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B) | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_B @ sk_F)))),
% 0.20/0.55      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.20/0.55  thf('23', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('24', plain, ((r2_hidden @ sk_F @ (k1_connsp_2 @ sk_B @ sk_F))),
% 0.20/0.55      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.55  thf('25', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X27 : $i, X28 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X27)
% 0.20/0.55          | ~ (m1_subset_1 @ X28 @ X27)
% 0.20/0.55          | ((k6_domain_1 @ X27 @ X28) = (k1_tarski @ X28)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F) = (k1_tarski @ sk_F))
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((r2_hidden @ sk_G @ 
% 0.20/0.55        (k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55         sk_D_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (((r2_hidden @ sk_G @ 
% 0.20/0.55         (k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55          sk_D_2 @ (k1_tarski @ sk_F)))
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.55          | ((k8_relset_1 @ X20 @ X21 @ X19 @ X22) = (k10_relat_1 @ X19 @ X22)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55           sk_D_2 @ X0) = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (((r2_hidden @ sk_G @ (k10_relat_1 @ sk_D_2 @ (k1_tarski @ sk_F)))
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['29', '32'])).
% 0.20/0.55  thf(d13_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.55       ( ![B:$i,C:$i]:
% 0.20/0.55         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.20/0.55           ( ![D:$i]:
% 0.20/0.55             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.55                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.55         (((X16) != (k10_relat_1 @ X15 @ X14))
% 0.20/0.55          | (r2_hidden @ (k1_funct_1 @ X15 @ X17) @ X14)
% 0.20/0.55          | ~ (r2_hidden @ X17 @ X16)
% 0.20/0.55          | ~ (v1_funct_1 @ X15)
% 0.20/0.55          | ~ (v1_relat_1 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X15)
% 0.20/0.55          | ~ (v1_funct_1 @ X15)
% 0.20/0.55          | ~ (r2_hidden @ X17 @ (k10_relat_1 @ X15 @ X14))
% 0.20/0.55          | (r2_hidden @ (k1_funct_1 @ X15 @ X17) @ X14))),
% 0.20/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.55        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_G) @ (k1_tarski @ sk_F))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.55        | ~ (v1_relat_1 @ sk_D_2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.55  thf('37', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc2_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.55          | (v1_relat_1 @ X9)
% 0.20/0.55          | ~ (v1_relat_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ 
% 0.20/0.55           (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v1_relat_1 @ sk_D_2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.55  thf(fc6_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.55  thf('42', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.55        | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_G) @ (k1_tarski @ sk_F)))),
% 0.20/0.55      inference('demod', [status(thm)], ['36', '37', '42'])).
% 0.20/0.55  thf(d1_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X0 : $i, X3 : $i]:
% 0.20/0.55         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.55        | ((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['43', '45'])).
% 0.20/0.55  thf('47', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k1_connsp_2, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55       ( m1_subset_1 @
% 0.20/0.55         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X29)
% 0.20/0.55          | ~ (v2_pre_topc @ X29)
% 0.20/0.55          | (v2_struct_0 @ X29)
% 0.20/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.20/0.55          | (m1_subset_1 @ (k1_connsp_2 @ X29 @ X30) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_F) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v2_struct_0 @ sk_B)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_F) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.55        | (v2_struct_0 @ sk_B))),
% 0.20/0.55      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.20/0.55  thf('53', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      ((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_F) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.55      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf(t5_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.55          | ~ (v1_xboole_0 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_B @ sk_F)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_B @ sk_F)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['46', '56'])).
% 0.20/0.55  thf('58', plain, (((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            sk_D_2 @ sk_G) = (sk_F)))),
% 0.20/0.55      inference('demod', [status(thm)], ['16', '58'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            sk_D_2 @ sk_G) = (sk_F)))),
% 0.20/0.55      inference('demod', [status(thm)], ['16', '58'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t52_tmap_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55             ( l1_pre_topc @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.20/0.55                 ( l1_pre_topc @ C ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.55                     ( v1_funct_2 @
% 0.20/0.55                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.55                     ( m1_subset_1 @
% 0.20/0.55                       D @ 
% 0.20/0.55                       ( k1_zfmisc_1 @
% 0.20/0.55                         ( k2_zfmisc_1 @
% 0.20/0.55                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                         ( v1_funct_2 @
% 0.20/0.55                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ 
% 0.20/0.55                           ( k1_zfmisc_1 @
% 0.20/0.55                             ( k2_zfmisc_1 @
% 0.20/0.55                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.55                       ( ![F:$i]:
% 0.20/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                           ( ![G:$i]:
% 0.20/0.55                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.55                               ( ( ( ( G ) =
% 0.20/0.55                                     ( k3_funct_2 @
% 0.20/0.55                                       ( u1_struct_0 @ B ) @ 
% 0.20/0.55                                       ( u1_struct_0 @ C ) @ D @ F ) ) & 
% 0.20/0.55                                   ( r1_tmap_1 @ B @ C @ D @ F ) & 
% 0.20/0.55                                   ( r1_tmap_1 @ C @ A @ E @ G ) ) =>
% 0.20/0.55                                 ( r1_tmap_1 @
% 0.20/0.55                                   B @ A @ 
% 0.20/0.55                                   ( k1_partfun1 @
% 0.20/0.55                                     ( u1_struct_0 @ B ) @ 
% 0.20/0.55                                     ( u1_struct_0 @ C ) @ 
% 0.20/0.55                                     ( u1_struct_0 @ C ) @ 
% 0.20/0.55                                     ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.20/0.55                                   F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X37)
% 0.20/0.55          | ~ (v2_pre_topc @ X37)
% 0.20/0.55          | ~ (l1_pre_topc @ X37)
% 0.20/0.55          | ~ (v1_funct_1 @ X38)
% 0.20/0.55          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.20/0.55          | ~ (m1_subset_1 @ X38 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 0.20/0.55          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X37))
% 0.20/0.55          | ~ (r1_tmap_1 @ X37 @ X39 @ X38 @ X40)
% 0.20/0.55          | (r1_tmap_1 @ X37 @ X41 @ 
% 0.20/0.55             (k1_partfun1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ 
% 0.20/0.55              (u1_struct_0 @ X39) @ (u1_struct_0 @ X41) @ X38 @ X42) @ 
% 0.20/0.55             X40)
% 0.20/0.55          | ((X43)
% 0.20/0.55              != (k3_funct_2 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ 
% 0.20/0.55                  X38 @ X40))
% 0.20/0.55          | ~ (r1_tmap_1 @ X39 @ X41 @ X42 @ X43)
% 0.20/0.55          | ~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X39))
% 0.20/0.55          | ~ (m1_subset_1 @ X42 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))))
% 0.20/0.55          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))
% 0.20/0.55          | ~ (v1_funct_1 @ X42)
% 0.20/0.55          | ~ (l1_pre_topc @ X39)
% 0.20/0.55          | ~ (v2_pre_topc @ X39)
% 0.20/0.55          | (v2_struct_0 @ X39)
% 0.20/0.55          | ~ (l1_pre_topc @ X41)
% 0.20/0.55          | ~ (v2_pre_topc @ X41)
% 0.20/0.55          | (v2_struct_0 @ X41))),
% 0.20/0.55      inference('cnf', [status(esa)], [t52_tmap_1])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X41)
% 0.20/0.55          | ~ (v2_pre_topc @ X41)
% 0.20/0.55          | ~ (l1_pre_topc @ X41)
% 0.20/0.55          | (v2_struct_0 @ X39)
% 0.20/0.55          | ~ (v2_pre_topc @ X39)
% 0.20/0.55          | ~ (l1_pre_topc @ X39)
% 0.20/0.55          | ~ (v1_funct_1 @ X42)
% 0.20/0.55          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))
% 0.20/0.55          | ~ (m1_subset_1 @ X42 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X41))))
% 0.20/0.55          | ~ (m1_subset_1 @ 
% 0.20/0.55               (k3_funct_2 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ X38 @ 
% 0.20/0.55                X40) @ 
% 0.20/0.55               (u1_struct_0 @ X39))
% 0.20/0.55          | ~ (r1_tmap_1 @ X39 @ X41 @ X42 @ 
% 0.20/0.55               (k3_funct_2 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ X38 @ 
% 0.20/0.55                X40))
% 0.20/0.55          | (r1_tmap_1 @ X37 @ X41 @ 
% 0.20/0.55             (k1_partfun1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ 
% 0.20/0.55              (u1_struct_0 @ X39) @ (u1_struct_0 @ X41) @ X38 @ X42) @ 
% 0.20/0.55             X40)
% 0.20/0.55          | ~ (r1_tmap_1 @ X37 @ X39 @ X38 @ X40)
% 0.20/0.55          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X37))
% 0.20/0.55          | ~ (m1_subset_1 @ X38 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 0.20/0.55          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 0.20/0.55          | ~ (v1_funct_1 @ X38)
% 0.20/0.55          | ~ (l1_pre_topc @ X37)
% 0.20/0.55          | ~ (v2_pre_topc @ X37)
% 0.20/0.55          | (v2_struct_0 @ X37))),
% 0.20/0.55      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X1)
% 0.20/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.55          | ~ (r1_tmap_1 @ X0 @ sk_B @ X1 @ X2)
% 0.20/0.55          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.55             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ sk_E) @ 
% 0.20/0.55             X2)
% 0.20/0.55          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ 
% 0.20/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.20/0.55                X2))
% 0.20/0.55          | ~ (m1_subset_1 @ 
% 0.20/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.20/0.55                X2) @ 
% 0.20/0.55               (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.55          | (v2_struct_0 @ sk_B)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['61', '63'])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('67', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('68', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X1)
% 0.20/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.55          | ~ (r1_tmap_1 @ X0 @ sk_B @ X1 @ X2)
% 0.20/0.55          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.55             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ sk_E) @ 
% 0.20/0.55             X2)
% 0.20/0.55          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ 
% 0.20/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.20/0.55                X2))
% 0.20/0.55          | ~ (m1_subset_1 @ 
% 0.20/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.20/0.55                X2) @ 
% 0.20/0.55               (u1_struct_0 @ sk_B))
% 0.20/0.55          | (v2_struct_0 @ sk_B)
% 0.20/0.55          | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)],
% 0.20/0.55                ['64', '65', '66', '67', '68', '69', '70'])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F)
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_B)
% 0.20/0.55        | ~ (m1_subset_1 @ 
% 0.20/0.55             (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55              sk_D_2 @ sk_G) @ 
% 0.20/0.55             (u1_struct_0 @ sk_B))
% 0.20/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.20/0.55           sk_G)
% 0.20/0.55        | ~ (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G)
% 0.20/0.55        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | ~ (m1_subset_1 @ sk_D_2 @ 
% 0.20/0.55             (k1_zfmisc_1 @ 
% 0.20/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))
% 0.20/0.55        | ~ (v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55             (u1_struct_0 @ sk_B))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_C_1)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_C_1)
% 0.20/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['60', '71'])).
% 0.20/0.55  thf('73', plain, ((r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('74', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t49_tmap_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.55             ( l1_pre_topc @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.55                 ( m1_subset_1 @
% 0.20/0.55                   C @ 
% 0.20/0.55                   ( k1_zfmisc_1 @
% 0.20/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.55               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.20/0.55                 ( ![D:$i]:
% 0.20/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X33)
% 0.20/0.55          | ~ (v2_pre_topc @ X33)
% 0.20/0.55          | ~ (l1_pre_topc @ X33)
% 0.20/0.55          | ~ (v5_pre_topc @ X34 @ X33 @ X35)
% 0.20/0.55          | (r1_tmap_1 @ X33 @ X35 @ X34 @ X36)
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X33))
% 0.20/0.55          | ~ (m1_subset_1 @ X34 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X35))))
% 0.20/0.55          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X35))
% 0.20/0.55          | ~ (v1_funct_1 @ X34)
% 0.20/0.55          | ~ (l1_pre_topc @ X35)
% 0.20/0.55          | ~ (v2_pre_topc @ X35)
% 0.20/0.55          | (v2_struct_0 @ X35))),
% 0.20/0.55      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.55               (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0)
% 0.20/0.55          | ~ (v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.20/0.55          | ~ (l1_pre_topc @ sk_C_1)
% 0.20/0.55          | ~ (v2_pre_topc @ sk_C_1)
% 0.20/0.55          | (v2_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.55  thf('78', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('80', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('82', plain, ((v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('83', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('84', plain, ((v2_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_B)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0)
% 0.20/0.55          | (v2_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('demod', [status(thm)],
% 0.20/0.55                ['77', '78', '79', '80', '81', '82', '83', '84'])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_C_1)
% 0.20/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G)
% 0.20/0.55        | (v2_struct_0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['74', '85'])).
% 0.20/0.55  thf('87', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B) | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G))),
% 0.20/0.55      inference('clc', [status(thm)], ['86', '87'])).
% 0.20/0.55  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('90', plain, ((r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G)),
% 0.20/0.55      inference('clc', [status(thm)], ['88', '89'])).
% 0.20/0.55  thf('91', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('94', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('95', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('96', plain, ((v2_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_B)
% 0.20/0.55        | ~ (m1_subset_1 @ 
% 0.20/0.55             (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55              sk_D_2 @ sk_G) @ 
% 0.20/0.55             (u1_struct_0 @ sk_B))
% 0.20/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.20/0.55           sk_G)
% 0.20/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('demod', [status(thm)],
% 0.20/0.55                ['72', '73', '90', '91', '92', '93', '94', '95', '96'])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | (v2_struct_0 @ sk_C_1)
% 0.20/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.20/0.55           sk_G)
% 0.20/0.55        | (v2_struct_0 @ sk_B)
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['59', '97'])).
% 0.20/0.55  thf('99', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('100', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | (v2_struct_0 @ sk_C_1)
% 0.20/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.20/0.55           sk_G)
% 0.20/0.55        | (v2_struct_0 @ sk_B)
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.55  thf('101', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_B)
% 0.20/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.20/0.55           sk_G)
% 0.20/0.55        | (v2_struct_0 @ sk_C_1)
% 0.20/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['100'])).
% 0.20/0.55  thf('102', plain,
% 0.20/0.55      (~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.20/0.55          (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.55           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.20/0.55          sk_G)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('103', plain,
% 0.20/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55        | (v2_struct_0 @ sk_C_1)
% 0.20/0.55        | (v2_struct_0 @ sk_B)
% 0.20/0.55        | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.55  thf('104', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('105', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X29)
% 0.20/0.55          | ~ (v2_pre_topc @ X29)
% 0.20/0.55          | (v2_struct_0 @ X29)
% 0.20/0.55          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.20/0.55          | (m1_subset_1 @ (k1_connsp_2 @ X29 @ X30) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.20/0.55  thf('106', plain,
% 0.20/0.55      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_G) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.55        | (v2_struct_0 @ sk_C_1)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_C_1)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['104', '105'])).
% 0.20/0.55  thf('107', plain, ((v2_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('108', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('109', plain,
% 0.20/0.55      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_G) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.20/0.55  thf('110', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('111', plain,
% 0.20/0.55      ((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_G) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.55      inference('clc', [status(thm)], ['109', '110'])).
% 0.20/0.55  thf('112', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.55          | ~ (v1_xboole_0 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.55  thf('113', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C_1 @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ sk_A)
% 0.20/0.55          | (v2_struct_0 @ sk_B)
% 0.20/0.55          | (v2_struct_0 @ sk_C_1)
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C_1 @ sk_G)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['103', '113'])).
% 0.20/0.55  thf('115', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '114'])).
% 0.20/0.55  thf('116', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('117', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.20/0.55      inference('clc', [status(thm)], ['115', '116'])).
% 0.20/0.55  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('119', plain, ((v2_struct_0 @ sk_B)),
% 0.20/0.55      inference('clc', [status(thm)], ['117', '118'])).
% 0.20/0.55  thf('120', plain, ($false), inference('demod', [status(thm)], ['0', '119'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
