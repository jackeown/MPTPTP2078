%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SVtpZBTCCY

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:35 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 286 expanded)
%              Number of leaves         :   41 ( 103 expanded)
%              Depth                    :   24
%              Number of atoms          : 1579 (11794 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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

thf('2',plain,(
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

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ X19 )
      | ( ( k3_funct_2 @ X19 @ X20 @ X18 @ X21 )
        = ( k1_funct_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ X0 )
        = ( k1_funct_1 @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ X0 )
        = ( k1_funct_1 @ sk_D_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G )
      = ( k1_funct_1 @ sk_D_2 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( ( k6_domain_1 @ X24 @ X25 )
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('11',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F )
      = ( k1_tarski @ sk_F ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_G @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k8_relset_1 @ X15 @ X16 @ X14 @ X17 )
        = ( k10_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ sk_G @ ( k10_relat_1 @ sk_D_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['12','15'])).

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

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k10_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X9 ) @ X6 )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k10_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X9 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_G ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_G ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_G ) @ ( k1_tarski @ sk_F ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','24'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_G )
      = sk_F ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('30',plain,
    ( ( ( k1_funct_1 @ sk_D_2 @ sk_G )
      = sk_F )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('32',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_funct_1 @ sk_D_2 @ sk_G )
      = sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_G )
    = sk_F ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G )
      = sk_F ) ),
    inference(demod,[status(thm)],['8','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G )
      = sk_F ) ),
    inference(demod,[status(thm)],['8','36'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r1_tmap_1 @ X30 @ X32 @ X31 @ X33 )
      | ( r1_tmap_1 @ X30 @ X34 @ ( k1_partfun1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X34 ) @ X31 @ X35 ) @ X33 )
      | ( X36
       != ( k3_funct_2 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) @ X31 @ X33 ) )
      | ~ ( r1_tmap_1 @ X32 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t52_tmap_1])).

thf('41',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) @ X31 @ X33 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( r1_tmap_1 @ X32 @ X34 @ X35 @ ( k3_funct_2 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) @ X31 @ X33 ) )
      | ( r1_tmap_1 @ X30 @ X34 @ ( k1_partfun1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X34 ) @ X31 @ X35 ) @ X33 )
      | ~ ( r1_tmap_1 @ X30 @ X32 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
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
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
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
    inference(demod,[status(thm)],['42','43','44','45','46','47','48'])).

thf('50',plain,
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
    inference('sup-',[status(thm)],['38','49'])).

thf('51',plain,(
    r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v5_pre_topc @ X27 @ X26 @ X28 )
      | ( r1_tmap_1 @ X26 @ X28 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('55',plain,(
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59','60','61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G ) @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51','68','69','70','71','72','73','74'])).

thf('76',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('86',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SVtpZBTCCY
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 122 iterations in 0.091s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.55  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.35/0.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.35/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.35/0.55  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.35/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.35/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.55  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.35/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.35/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.35/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(t53_tmap_1, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.35/0.55             ( l1_pre_topc @ B ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.35/0.55                 ( l1_pre_topc @ C ) ) =>
% 0.35/0.55               ( ![D:$i]:
% 0.35/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.35/0.55                     ( v1_funct_2 @
% 0.35/0.55                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.35/0.55                     ( m1_subset_1 @
% 0.35/0.55                       D @ 
% 0.35/0.55                       ( k1_zfmisc_1 @
% 0.35/0.55                         ( k2_zfmisc_1 @
% 0.35/0.55                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.35/0.55                   ( ![E:$i]:
% 0.35/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.55                         ( v1_funct_2 @
% 0.35/0.55                           E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.55                         ( m1_subset_1 @
% 0.35/0.55                           E @ 
% 0.35/0.55                           ( k1_zfmisc_1 @
% 0.35/0.55                             ( k2_zfmisc_1 @
% 0.35/0.55                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.35/0.55                       ( ![F:$i]:
% 0.35/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.35/0.55                           ( ( ( v5_pre_topc @ D @ C @ B ) & 
% 0.35/0.55                               ( r1_tmap_1 @ B @ A @ E @ F ) ) =>
% 0.35/0.55                             ( ![G:$i]:
% 0.35/0.55                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.35/0.55                                 ( ( r2_hidden @
% 0.35/0.55                                     G @ 
% 0.35/0.55                                     ( k8_relset_1 @
% 0.35/0.55                                       ( u1_struct_0 @ C ) @ 
% 0.35/0.55                                       ( u1_struct_0 @ B ) @ D @ 
% 0.35/0.55                                       ( k6_domain_1 @ ( u1_struct_0 @ B ) @ F ) ) ) =>
% 0.35/0.55                                   ( r1_tmap_1 @
% 0.35/0.55                                     C @ A @ 
% 0.35/0.55                                     ( k1_partfun1 @
% 0.35/0.55                                       ( u1_struct_0 @ C ) @ 
% 0.35/0.55                                       ( u1_struct_0 @ B ) @ 
% 0.35/0.55                                       ( u1_struct_0 @ B ) @ 
% 0.35/0.55                                       ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.35/0.55                                     G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.55            ( l1_pre_topc @ A ) ) =>
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.35/0.55                ( l1_pre_topc @ B ) ) =>
% 0.35/0.55              ( ![C:$i]:
% 0.35/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.35/0.55                    ( l1_pre_topc @ C ) ) =>
% 0.35/0.55                  ( ![D:$i]:
% 0.35/0.55                    ( ( ( v1_funct_1 @ D ) & 
% 0.35/0.55                        ( v1_funct_2 @
% 0.35/0.55                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.35/0.55                        ( m1_subset_1 @
% 0.35/0.55                          D @ 
% 0.35/0.55                          ( k1_zfmisc_1 @
% 0.35/0.55                            ( k2_zfmisc_1 @
% 0.35/0.55                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.35/0.55                      ( ![E:$i]:
% 0.35/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.55                            ( v1_funct_2 @
% 0.35/0.55                              E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.55                            ( m1_subset_1 @
% 0.35/0.55                              E @ 
% 0.35/0.55                              ( k1_zfmisc_1 @
% 0.35/0.55                                ( k2_zfmisc_1 @
% 0.35/0.55                                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.35/0.55                          ( ![F:$i]:
% 0.35/0.55                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.35/0.55                              ( ( ( v5_pre_topc @ D @ C @ B ) & 
% 0.35/0.55                                  ( r1_tmap_1 @ B @ A @ E @ F ) ) =>
% 0.35/0.55                                ( ![G:$i]:
% 0.35/0.55                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.35/0.55                                    ( ( r2_hidden @
% 0.35/0.55                                        G @ 
% 0.35/0.55                                        ( k8_relset_1 @
% 0.35/0.55                                          ( u1_struct_0 @ C ) @ 
% 0.35/0.55                                          ( u1_struct_0 @ B ) @ D @ 
% 0.35/0.55                                          ( k6_domain_1 @
% 0.35/0.55                                            ( u1_struct_0 @ B ) @ F ) ) ) =>
% 0.35/0.55                                      ( r1_tmap_1 @
% 0.35/0.55                                        C @ A @ 
% 0.35/0.55                                        ( k1_partfun1 @
% 0.35/0.55                                          ( u1_struct_0 @ C ) @ 
% 0.35/0.55                                          ( u1_struct_0 @ B ) @ 
% 0.35/0.55                                          ( u1_struct_0 @ B ) @ 
% 0.35/0.55                                          ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.35/0.55                                        G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t53_tmap_1])).
% 0.35/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.35/0.55        (k1_zfmisc_1 @ 
% 0.35/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k3_funct_2, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.35/0.55         ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.55         ( m1_subset_1 @ D @ A ) ) =>
% 0.35/0.55       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.35/0.55          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.35/0.55          | ~ (v1_funct_1 @ X18)
% 0.35/0.55          | (v1_xboole_0 @ X19)
% 0.35/0.55          | ~ (m1_subset_1 @ X21 @ X19)
% 0.35/0.55          | ((k3_funct_2 @ X19 @ X20 @ X18 @ X21) = (k1_funct_1 @ X18 @ X21)))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            sk_D_2 @ X0) = (k1_funct_1 @ sk_D_2 @ X0))
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55          | ~ (v1_funct_1 @ sk_D_2)
% 0.35/0.55          | ~ (v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ 
% 0.35/0.55               (u1_struct_0 @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.55  thf('5', plain, ((v1_funct_1 @ sk_D_2)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      ((v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            sk_D_2 @ X0) = (k1_funct_1 @ sk_D_2 @ X0))
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            sk_D_2 @ sk_G) = (k1_funct_1 @ sk_D_2 @ sk_G)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['1', '7'])).
% 0.35/0.55  thf('9', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X24 : $i, X25 : $i]:
% 0.35/0.55         ((v1_xboole_0 @ X24)
% 0.35/0.55          | ~ (m1_subset_1 @ X25 @ X24)
% 0.35/0.55          | ((k6_domain_1 @ X24 @ X25) = (k1_tarski @ X25)))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.35/0.55  thf('11', plain,
% 0.35/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F) = (k1_tarski @ sk_F))
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      ((r2_hidden @ sk_G @ 
% 0.35/0.55        (k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55         sk_D_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.35/0.55        (k1_zfmisc_1 @ 
% 0.35/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k8_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.35/0.55          | ((k8_relset_1 @ X15 @ X16 @ X14 @ X17) = (k10_relat_1 @ X14 @ X17)))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55           sk_D_2 @ X0) = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      ((r2_hidden @ sk_G @ 
% 0.35/0.55        (k10_relat_1 @ sk_D_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F)))),
% 0.35/0.55      inference('demod', [status(thm)], ['12', '15'])).
% 0.35/0.55  thf(d13_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ![B:$i,C:$i]:
% 0.35/0.55         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.35/0.55           ( ![D:$i]:
% 0.35/0.55             ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.55               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.35/0.55                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.55         (((X8) != (k10_relat_1 @ X7 @ X6))
% 0.35/0.55          | (r2_hidden @ (k1_funct_1 @ X7 @ X9) @ X6)
% 0.35/0.55          | ~ (r2_hidden @ X9 @ X8)
% 0.35/0.55          | ~ (v1_funct_1 @ X7)
% 0.35/0.55          | ~ (v1_relat_1 @ X7))),
% 0.35/0.55      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.35/0.55         (~ (v1_relat_1 @ X7)
% 0.35/0.55          | ~ (v1_funct_1 @ X7)
% 0.35/0.55          | ~ (r2_hidden @ X9 @ (k10_relat_1 @ X7 @ X6))
% 0.35/0.55          | (r2_hidden @ (k1_funct_1 @ X7 @ X9) @ X6))),
% 0.35/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.55  thf('19', plain,
% 0.35/0.55      (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_G) @ 
% 0.35/0.55         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F))
% 0.35/0.55        | ~ (v1_funct_1 @ sk_D_2)
% 0.35/0.55        | ~ (v1_relat_1 @ sk_D_2))),
% 0.35/0.55      inference('sup-', [status(thm)], ['16', '18'])).
% 0.35/0.55  thf('20', plain, ((v1_funct_1 @ sk_D_2)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.35/0.55        (k1_zfmisc_1 @ 
% 0.35/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(cc1_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( v1_relat_1 @ C ) ))).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.55         ((v1_relat_1 @ X11)
% 0.35/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.55  thf('23', plain, ((v1_relat_1 @ sk_D_2)),
% 0.35/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_G) @ 
% 0.35/0.55        (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F))),
% 0.35/0.55      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_G) @ (k1_tarski @ sk_F))
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['11', '24'])).
% 0.35/0.55  thf(d1_tarski, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      (![X0 : $i, X3 : $i]:
% 0.35/0.55         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.35/0.55        | ((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['25', '27'])).
% 0.35/0.55  thf(fc2_struct_0, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      (![X23 : $i]:
% 0.35/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.35/0.55          | ~ (l1_struct_0 @ X23)
% 0.35/0.55          | (v2_struct_0 @ X23))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      ((((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F))
% 0.35/0.55        | (v2_struct_0 @ sk_B)
% 0.35/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.55  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(dt_l1_pre_topc, axiom,
% 0.35/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.55  thf('33', plain, ((l1_struct_0 @ sk_B)),
% 0.35/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      ((((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F)) | (v2_struct_0 @ sk_B))),
% 0.35/0.55      inference('demod', [status(thm)], ['30', '33'])).
% 0.35/0.55  thf('35', plain, (~ (v2_struct_0 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('36', plain, (((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F))),
% 0.35/0.55      inference('clc', [status(thm)], ['34', '35'])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            sk_D_2 @ sk_G) = (sk_F)))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '36'])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            sk_D_2 @ sk_G) = (sk_F)))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '36'])).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_E @ 
% 0.35/0.55        (k1_zfmisc_1 @ 
% 0.35/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t52_tmap_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.35/0.55             ( l1_pre_topc @ B ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.35/0.55                 ( l1_pre_topc @ C ) ) =>
% 0.35/0.55               ( ![D:$i]:
% 0.35/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.35/0.55                     ( v1_funct_2 @
% 0.35/0.55                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.35/0.55                     ( m1_subset_1 @
% 0.35/0.55                       D @ 
% 0.35/0.55                       ( k1_zfmisc_1 @
% 0.35/0.55                         ( k2_zfmisc_1 @
% 0.35/0.55                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.35/0.55                   ( ![E:$i]:
% 0.35/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.35/0.55                         ( v1_funct_2 @
% 0.35/0.55                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.55                         ( m1_subset_1 @
% 0.35/0.55                           E @ 
% 0.35/0.55                           ( k1_zfmisc_1 @
% 0.35/0.55                             ( k2_zfmisc_1 @
% 0.35/0.55                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.35/0.55                       ( ![F:$i]:
% 0.35/0.55                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.35/0.55                           ( ![G:$i]:
% 0.35/0.55                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.35/0.55                               ( ( ( ( G ) =
% 0.35/0.55                                     ( k3_funct_2 @
% 0.35/0.55                                       ( u1_struct_0 @ B ) @ 
% 0.35/0.55                                       ( u1_struct_0 @ C ) @ D @ F ) ) & 
% 0.35/0.55                                   ( r1_tmap_1 @ B @ C @ D @ F ) & 
% 0.35/0.55                                   ( r1_tmap_1 @ C @ A @ E @ G ) ) =>
% 0.35/0.55                                 ( r1_tmap_1 @
% 0.35/0.55                                   B @ A @ 
% 0.35/0.55                                   ( k1_partfun1 @
% 0.35/0.55                                     ( u1_struct_0 @ B ) @ 
% 0.35/0.55                                     ( u1_struct_0 @ C ) @ 
% 0.35/0.55                                     ( u1_struct_0 @ C ) @ 
% 0.35/0.55                                     ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.35/0.55                                   F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.35/0.55         ((v2_struct_0 @ X30)
% 0.35/0.55          | ~ (v2_pre_topc @ X30)
% 0.35/0.55          | ~ (l1_pre_topc @ X30)
% 0.35/0.55          | ~ (v1_funct_1 @ X31)
% 0.35/0.55          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32))
% 0.35/0.55          | ~ (m1_subset_1 @ X31 @ 
% 0.35/0.55               (k1_zfmisc_1 @ 
% 0.35/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32))))
% 0.35/0.55          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X30))
% 0.35/0.55          | ~ (r1_tmap_1 @ X30 @ X32 @ X31 @ X33)
% 0.35/0.55          | (r1_tmap_1 @ X30 @ X34 @ 
% 0.35/0.55             (k1_partfun1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32) @ 
% 0.35/0.55              (u1_struct_0 @ X32) @ (u1_struct_0 @ X34) @ X31 @ X35) @ 
% 0.35/0.55             X33)
% 0.35/0.55          | ((X36)
% 0.35/0.55              != (k3_funct_2 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32) @ 
% 0.35/0.55                  X31 @ X33))
% 0.35/0.55          | ~ (r1_tmap_1 @ X32 @ X34 @ X35 @ X36)
% 0.35/0.55          | ~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X32))
% 0.35/0.55          | ~ (m1_subset_1 @ X35 @ 
% 0.35/0.55               (k1_zfmisc_1 @ 
% 0.35/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X34))))
% 0.35/0.55          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X34))
% 0.35/0.55          | ~ (v1_funct_1 @ X35)
% 0.35/0.55          | ~ (l1_pre_topc @ X32)
% 0.35/0.55          | ~ (v2_pre_topc @ X32)
% 0.35/0.55          | (v2_struct_0 @ X32)
% 0.35/0.55          | ~ (l1_pre_topc @ X34)
% 0.35/0.55          | ~ (v2_pre_topc @ X34)
% 0.35/0.55          | (v2_struct_0 @ X34))),
% 0.35/0.55      inference('cnf', [status(esa)], [t52_tmap_1])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.55         ((v2_struct_0 @ X34)
% 0.35/0.55          | ~ (v2_pre_topc @ X34)
% 0.35/0.55          | ~ (l1_pre_topc @ X34)
% 0.35/0.55          | (v2_struct_0 @ X32)
% 0.35/0.55          | ~ (v2_pre_topc @ X32)
% 0.35/0.55          | ~ (l1_pre_topc @ X32)
% 0.35/0.55          | ~ (v1_funct_1 @ X35)
% 0.35/0.55          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X34))
% 0.35/0.55          | ~ (m1_subset_1 @ X35 @ 
% 0.35/0.55               (k1_zfmisc_1 @ 
% 0.35/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X34))))
% 0.35/0.55          | ~ (m1_subset_1 @ 
% 0.35/0.55               (k3_funct_2 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32) @ X31 @ 
% 0.35/0.55                X33) @ 
% 0.35/0.55               (u1_struct_0 @ X32))
% 0.35/0.55          | ~ (r1_tmap_1 @ X32 @ X34 @ X35 @ 
% 0.35/0.55               (k3_funct_2 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32) @ X31 @ 
% 0.35/0.55                X33))
% 0.35/0.55          | (r1_tmap_1 @ X30 @ X34 @ 
% 0.35/0.55             (k1_partfun1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32) @ 
% 0.35/0.55              (u1_struct_0 @ X32) @ (u1_struct_0 @ X34) @ X31 @ X35) @ 
% 0.35/0.55             X33)
% 0.35/0.55          | ~ (r1_tmap_1 @ X30 @ X32 @ X31 @ X33)
% 0.35/0.55          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X30))
% 0.35/0.55          | ~ (m1_subset_1 @ X31 @ 
% 0.35/0.55               (k1_zfmisc_1 @ 
% 0.35/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32))))
% 0.35/0.55          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32))
% 0.35/0.55          | ~ (v1_funct_1 @ X31)
% 0.35/0.55          | ~ (l1_pre_topc @ X30)
% 0.35/0.55          | ~ (v2_pre_topc @ X30)
% 0.35/0.55          | (v2_struct_0 @ X30))),
% 0.35/0.55      inference('simplify', [status(thm)], ['40'])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         ((v2_struct_0 @ X0)
% 0.35/0.55          | ~ (v2_pre_topc @ X0)
% 0.35/0.55          | ~ (l1_pre_topc @ X0)
% 0.35/0.55          | ~ (v1_funct_1 @ X1)
% 0.35/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.35/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.35/0.55               (k1_zfmisc_1 @ 
% 0.35/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.35/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.35/0.55          | ~ (r1_tmap_1 @ X0 @ sk_B @ X1 @ X2)
% 0.35/0.55          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.35/0.55             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ sk_E) @ 
% 0.35/0.55             X2)
% 0.35/0.55          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ 
% 0.35/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.35/0.55                X2))
% 0.35/0.55          | ~ (m1_subset_1 @ 
% 0.35/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.35/0.55                X2) @ 
% 0.35/0.55               (u1_struct_0 @ sk_B))
% 0.35/0.55          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.35/0.55          | ~ (v1_funct_1 @ sk_E)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.35/0.55          | (v2_struct_0 @ sk_B)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.55          | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['39', '41'])).
% 0.35/0.55  thf('43', plain,
% 0.35/0.55      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('44', plain, ((v1_funct_1 @ sk_E)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('46', plain, ((v2_pre_topc @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('49', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.55         ((v2_struct_0 @ X0)
% 0.35/0.55          | ~ (v2_pre_topc @ X0)
% 0.35/0.55          | ~ (l1_pre_topc @ X0)
% 0.35/0.55          | ~ (v1_funct_1 @ X1)
% 0.35/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.35/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.35/0.55               (k1_zfmisc_1 @ 
% 0.35/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.35/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.35/0.55          | ~ (r1_tmap_1 @ X0 @ sk_B @ X1 @ X2)
% 0.35/0.55          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.35/0.55             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ sk_E) @ 
% 0.35/0.55             X2)
% 0.35/0.55          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ 
% 0.35/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.35/0.55                X2))
% 0.35/0.55          | ~ (m1_subset_1 @ 
% 0.35/0.55               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.35/0.55                X2) @ 
% 0.35/0.55               (u1_struct_0 @ sk_B))
% 0.35/0.55          | (v2_struct_0 @ sk_B)
% 0.35/0.55          | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)],
% 0.35/0.55                ['42', '43', '44', '45', '46', '47', '48'])).
% 0.35/0.55  thf('50', plain,
% 0.35/0.55      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F)
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | (v2_struct_0 @ sk_B)
% 0.35/0.55        | ~ (m1_subset_1 @ 
% 0.35/0.55             (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55              sk_D_2 @ sk_G) @ 
% 0.35/0.55             (u1_struct_0 @ sk_B))
% 0.35/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.35/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.35/0.55           sk_G)
% 0.35/0.55        | ~ (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G)
% 0.35/0.55        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55        | ~ (m1_subset_1 @ sk_D_2 @ 
% 0.35/0.55             (k1_zfmisc_1 @ 
% 0.35/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))
% 0.35/0.55        | ~ (v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ 
% 0.35/0.55             (u1_struct_0 @ sk_B))
% 0.35/0.55        | ~ (v1_funct_1 @ sk_D_2)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_C_1)
% 0.35/0.55        | ~ (v2_pre_topc @ sk_C_1)
% 0.35/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['38', '49'])).
% 0.35/0.55  thf('51', plain, ((r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('52', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('53', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.35/0.55        (k1_zfmisc_1 @ 
% 0.35/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t49_tmap_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.35/0.55             ( l1_pre_topc @ B ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.35/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.35/0.55                 ( m1_subset_1 @
% 0.35/0.55                   C @ 
% 0.35/0.55                   ( k1_zfmisc_1 @
% 0.35/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.35/0.55               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.35/0.55                 ( ![D:$i]:
% 0.35/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.35/0.55                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('54', plain,
% 0.35/0.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.35/0.55         ((v2_struct_0 @ X26)
% 0.35/0.55          | ~ (v2_pre_topc @ X26)
% 0.35/0.55          | ~ (l1_pre_topc @ X26)
% 0.35/0.55          | ~ (v5_pre_topc @ X27 @ X26 @ X28)
% 0.35/0.55          | (r1_tmap_1 @ X26 @ X28 @ X27 @ X29)
% 0.35/0.55          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 0.35/0.55          | ~ (m1_subset_1 @ X27 @ 
% 0.35/0.55               (k1_zfmisc_1 @ 
% 0.35/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X28))))
% 0.35/0.55          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X28))
% 0.35/0.55          | ~ (v1_funct_1 @ X27)
% 0.35/0.55          | ~ (l1_pre_topc @ X28)
% 0.35/0.55          | ~ (v2_pre_topc @ X28)
% 0.35/0.55          | (v2_struct_0 @ X28))),
% 0.35/0.55      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.35/0.55  thf('55', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_B)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.35/0.55          | ~ (v1_funct_1 @ sk_D_2)
% 0.35/0.55          | ~ (v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ 
% 0.35/0.55               (u1_struct_0 @ sk_B))
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55          | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0)
% 0.35/0.55          | ~ (v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.35/0.55          | ~ (l1_pre_topc @ sk_C_1)
% 0.35/0.55          | ~ (v2_pre_topc @ sk_C_1)
% 0.35/0.55          | (v2_struct_0 @ sk_C_1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.35/0.55  thf('56', plain, ((v2_pre_topc @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('58', plain, ((v1_funct_1 @ sk_D_2)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('59', plain,
% 0.35/0.55      ((v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('60', plain, ((v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('61', plain, ((l1_pre_topc @ sk_C_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('62', plain, ((v2_pre_topc @ sk_C_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('63', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v2_struct_0 @ sk_B)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55          | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0)
% 0.35/0.55          | (v2_struct_0 @ sk_C_1))),
% 0.35/0.55      inference('demod', [status(thm)],
% 0.35/0.55                ['55', '56', '57', '58', '59', '60', '61', '62'])).
% 0.35/0.55  thf('64', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_C_1)
% 0.35/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G)
% 0.35/0.55        | (v2_struct_0 @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['52', '63'])).
% 0.35/0.55  thf('65', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('66', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_B) | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G))),
% 0.35/0.55      inference('clc', [status(thm)], ['64', '65'])).
% 0.35/0.55  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('68', plain, ((r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G)),
% 0.35/0.55      inference('clc', [status(thm)], ['66', '67'])).
% 0.35/0.55  thf('69', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('70', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_D_2 @ 
% 0.35/0.55        (k1_zfmisc_1 @ 
% 0.35/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('71', plain,
% 0.35/0.55      ((v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('72', plain, ((v1_funct_1 @ sk_D_2)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('73', plain, ((l1_pre_topc @ sk_C_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('74', plain, ((v2_pre_topc @ sk_C_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('75', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | (v2_struct_0 @ sk_B)
% 0.35/0.55        | ~ (m1_subset_1 @ 
% 0.35/0.55             (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55              sk_D_2 @ sk_G) @ 
% 0.35/0.55             (u1_struct_0 @ sk_B))
% 0.35/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.35/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.35/0.55           sk_G)
% 0.35/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.35/0.55      inference('demod', [status(thm)],
% 0.35/0.55                ['50', '51', '68', '69', '70', '71', '72', '73', '74'])).
% 0.35/0.55  thf('76', plain,
% 0.35/0.55      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55        | (v2_struct_0 @ sk_C_1)
% 0.35/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.35/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.35/0.55           sk_G)
% 0.35/0.55        | (v2_struct_0 @ sk_B)
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['37', '75'])).
% 0.35/0.55  thf('77', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('78', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55        | (v2_struct_0 @ sk_C_1)
% 0.35/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.35/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.35/0.55           sk_G)
% 0.35/0.55        | (v2_struct_0 @ sk_B)
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.35/0.55      inference('demod', [status(thm)], ['76', '77'])).
% 0.35/0.55  thf('79', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | (v2_struct_0 @ sk_B)
% 0.35/0.55        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.35/0.55           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.35/0.55           sk_G)
% 0.35/0.55        | (v2_struct_0 @ sk_C_1)
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['78'])).
% 0.35/0.55  thf('80', plain,
% 0.35/0.55      (~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.35/0.55          (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.35/0.55           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.35/0.55          sk_G)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('81', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.35/0.55        | (v2_struct_0 @ sk_C_1)
% 0.35/0.55        | (v2_struct_0 @ sk_B)
% 0.35/0.55        | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.35/0.55  thf('82', plain,
% 0.35/0.55      (![X23 : $i]:
% 0.35/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.35/0.55          | ~ (l1_struct_0 @ X23)
% 0.35/0.55          | (v2_struct_0 @ X23))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.55  thf('83', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | (v2_struct_0 @ sk_B)
% 0.35/0.55        | (v2_struct_0 @ sk_C_1)
% 0.35/0.55        | (v2_struct_0 @ sk_C_1)
% 0.35/0.55        | ~ (l1_struct_0 @ sk_C_1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['81', '82'])).
% 0.35/0.55  thf('84', plain, ((l1_pre_topc @ sk_C_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('85', plain,
% 0.35/0.55      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.55  thf('86', plain, ((l1_struct_0 @ sk_C_1)),
% 0.35/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.35/0.55  thf('87', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | (v2_struct_0 @ sk_B)
% 0.35/0.55        | (v2_struct_0 @ sk_C_1)
% 0.35/0.55        | (v2_struct_0 @ sk_C_1))),
% 0.35/0.55      inference('demod', [status(thm)], ['83', '86'])).
% 0.35/0.55  thf('88', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('simplify', [status(thm)], ['87'])).
% 0.35/0.55  thf('89', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('90', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.35/0.55      inference('clc', [status(thm)], ['88', '89'])).
% 0.35/0.55  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('92', plain, ((v2_struct_0 @ sk_B)),
% 0.35/0.55      inference('clc', [status(thm)], ['90', '91'])).
% 0.35/0.55  thf('93', plain, ($false), inference('demod', [status(thm)], ['0', '92'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
