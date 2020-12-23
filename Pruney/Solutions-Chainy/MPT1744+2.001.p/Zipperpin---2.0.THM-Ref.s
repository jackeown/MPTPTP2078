%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fThbn5W6CA

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:35 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 364 expanded)
%              Number of leaves         :   42 ( 125 expanded)
%              Depth                    :   22
%              Number of atoms          : 1806 (15751 expanded)
%              Number of equality atoms :   25 (  46 expanded)
%              Maximal formula depth    :   30 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_connsp_2_type,type,(
    k1_connsp_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( r2_hidden @ X30 @ ( k1_connsp_2 @ X31 @ X30 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ X23 )
      | ( ( k3_funct_2 @ X23 @ X24 @ X22 @ X25 )
        = ( k1_funct_1 @ X22 @ X25 ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ( r2_hidden @ X30 @ ( k1_connsp_2 @ X31 @ X30 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F )
      = ( k1_tarski @ sk_F ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_G @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k8_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k10_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ X0 )
      = ( k10_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_G @ ( k10_relat_1 @ sk_D_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['28','31'])).

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

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k10_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X13 ) @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k10_relat_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X13 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_G ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_G ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_G ) @ ( k1_tarski @ sk_F ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','40'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('43',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_D_2 @ sk_G )
      = sk_F ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_B @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_B @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_B @ sk_F ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_B @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D_2 @ sk_G )
        = sk_F )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_B @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_G )
    = sk_F ),
    inference('sup-',[status(thm)],['24','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G )
      = sk_F ) ),
    inference(demod,[status(thm)],['16','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G )
      = sk_F ) ),
    inference(demod,[status(thm)],['16','56'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_tmap_1 @ X36 @ X38 @ X37 @ X39 )
      | ( r1_tmap_1 @ X36 @ X40 @ ( k1_partfun1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) @ X37 @ X41 ) @ X39 )
      | ( X42
       != ( k3_funct_2 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) @ X37 @ X39 ) )
      | ~ ( r1_tmap_1 @ X38 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_tmap_1])).

thf('61',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) @ X37 @ X39 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( r1_tmap_1 @ X38 @ X40 @ X41 @ ( k3_funct_2 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) @ X37 @ X39 ) )
      | ( r1_tmap_1 @ X36 @ X40 @ ( k1_partfun1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) @ X37 @ X41 ) @ X39 )
      | ~ ( r1_tmap_1 @ X36 @ X38 @ X37 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
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
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
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
    inference(demod,[status(thm)],['62','63','64','65','66','67','68'])).

thf('70',plain,
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
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v5_pre_topc @ X33 @ X32 @ X34 )
      | ( r1_tmap_1 @ X32 @ X34 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('75',plain,(
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
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78','79','80','81','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_D_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_2 @ sk_G ) @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','71','88','89','90','91','92','93','94'])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['57','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_2 @ sk_E ) @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( m1_subset_1 @ ( k1_connsp_2 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_connsp_2])).

thf('104',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_connsp_2 @ sk_C_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['101','111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['0','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fThbn5W6CA
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 159 iterations in 0.113s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.38/0.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.58  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.58  thf(sk_G_type, type, sk_G: $i).
% 0.38/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.58  thf(k1_connsp_2_type, type, k1_connsp_2: $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.38/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.38/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.58  thf(t53_tmap_1, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.38/0.58                 ( l1_pre_topc @ C ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( ( v1_funct_1 @ D ) & 
% 0.38/0.58                     ( v1_funct_2 @
% 0.38/0.58                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                     ( m1_subset_1 @
% 0.38/0.58                       D @ 
% 0.38/0.58                       ( k1_zfmisc_1 @
% 0.38/0.58                         ( k2_zfmisc_1 @
% 0.38/0.58                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                   ( ![E:$i]:
% 0.38/0.58                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.58                         ( v1_funct_2 @
% 0.38/0.58                           E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.58                         ( m1_subset_1 @
% 0.38/0.58                           E @ 
% 0.38/0.58                           ( k1_zfmisc_1 @
% 0.38/0.58                             ( k2_zfmisc_1 @
% 0.38/0.58                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.58                       ( ![F:$i]:
% 0.38/0.58                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                           ( ( ( v5_pre_topc @ D @ C @ B ) & 
% 0.38/0.58                               ( r1_tmap_1 @ B @ A @ E @ F ) ) =>
% 0.38/0.58                             ( ![G:$i]:
% 0.38/0.58                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.58                                 ( ( r2_hidden @
% 0.38/0.58                                     G @ 
% 0.38/0.58                                     ( k8_relset_1 @
% 0.38/0.58                                       ( u1_struct_0 @ C ) @ 
% 0.38/0.58                                       ( u1_struct_0 @ B ) @ D @ 
% 0.38/0.58                                       ( k6_domain_1 @ ( u1_struct_0 @ B ) @ F ) ) ) =>
% 0.38/0.58                                   ( r1_tmap_1 @
% 0.38/0.58                                     C @ A @ 
% 0.38/0.58                                     ( k1_partfun1 @
% 0.38/0.58                                       ( u1_struct_0 @ C ) @ 
% 0.38/0.58                                       ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                       ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                       ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.38/0.58                                     G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.58            ( l1_pre_topc @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58                ( l1_pre_topc @ B ) ) =>
% 0.38/0.58              ( ![C:$i]:
% 0.38/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.38/0.58                    ( l1_pre_topc @ C ) ) =>
% 0.38/0.58                  ( ![D:$i]:
% 0.38/0.58                    ( ( ( v1_funct_1 @ D ) & 
% 0.38/0.58                        ( v1_funct_2 @
% 0.38/0.58                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.58                        ( m1_subset_1 @
% 0.38/0.58                          D @ 
% 0.38/0.58                          ( k1_zfmisc_1 @
% 0.38/0.58                            ( k2_zfmisc_1 @
% 0.38/0.58                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.58                      ( ![E:$i]:
% 0.38/0.58                        ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.58                            ( v1_funct_2 @
% 0.38/0.58                              E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.58                            ( m1_subset_1 @
% 0.38/0.58                              E @ 
% 0.38/0.58                              ( k1_zfmisc_1 @
% 0.38/0.58                                ( k2_zfmisc_1 @
% 0.38/0.58                                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.58                          ( ![F:$i]:
% 0.38/0.58                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                              ( ( ( v5_pre_topc @ D @ C @ B ) & 
% 0.38/0.58                                  ( r1_tmap_1 @ B @ A @ E @ F ) ) =>
% 0.38/0.58                                ( ![G:$i]:
% 0.38/0.58                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.58                                    ( ( r2_hidden @
% 0.38/0.58                                        G @ 
% 0.38/0.58                                        ( k8_relset_1 @
% 0.38/0.58                                          ( u1_struct_0 @ C ) @ 
% 0.38/0.58                                          ( u1_struct_0 @ B ) @ D @ 
% 0.38/0.58                                          ( k6_domain_1 @
% 0.38/0.58                                            ( u1_struct_0 @ B ) @ F ) ) ) =>
% 0.38/0.58                                      ( r1_tmap_1 @
% 0.38/0.58                                        C @ A @ 
% 0.38/0.58                                        ( k1_partfun1 @
% 0.38/0.58                                          ( u1_struct_0 @ C ) @ 
% 0.38/0.58                                          ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                          ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                          ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.38/0.58                                        G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t53_tmap_1])).
% 0.38/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t30_connsp_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58           ( r2_hidden @ B @ ( k1_connsp_2 @ A @ B ) ) ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X30 : $i, X31 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.38/0.58          | (r2_hidden @ X30 @ (k1_connsp_2 @ X31 @ X30))
% 0.38/0.58          | ~ (l1_pre_topc @ X31)
% 0.38/0.58          | ~ (v2_pre_topc @ X31)
% 0.38/0.58          | (v2_struct_0 @ X31))),
% 0.38/0.58      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_C_1)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_C_1)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_C_1)
% 0.38/0.58        | (r2_hidden @ sk_G @ (k1_connsp_2 @ sk_C_1 @ sk_G)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('4', plain, ((v2_pre_topc @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('5', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (r2_hidden @ sk_G @ (k1_connsp_2 @ sk_C_1 @ sk_G)))),
% 0.38/0.58      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.58  thf('7', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('8', plain, ((r2_hidden @ sk_G @ (k1_connsp_2 @ sk_C_1 @ sk_G))),
% 0.38/0.58      inference('clc', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf('9', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(redefinition_k3_funct_2, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.38/0.58         ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.58         ( m1_subset_1 @ D @ A ) ) =>
% 0.38/0.58       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.38/0.58          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.38/0.58          | ~ (v1_funct_1 @ X22)
% 0.38/0.58          | (v1_xboole_0 @ X23)
% 0.38/0.58          | ~ (m1_subset_1 @ X25 @ X23)
% 0.38/0.58          | ((k3_funct_2 @ X23 @ X24 @ X22 @ X25) = (k1_funct_1 @ X22 @ X25)))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            sk_D_2 @ X0) = (k1_funct_1 @ sk_D_2 @ X0))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | ~ (v1_funct_1 @ sk_D_2)
% 0.38/0.58          | ~ (v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.58  thf('13', plain, ((v1_funct_1 @ sk_D_2)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            sk_D_2 @ X0) = (k1_funct_1 @ sk_D_2 @ X0))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            sk_D_2 @ sk_G) = (k1_funct_1 @ sk_D_2 @ sk_G)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '15'])).
% 0.38/0.58  thf('17', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X30 : $i, X31 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.38/0.58          | (r2_hidden @ X30 @ (k1_connsp_2 @ X31 @ X30))
% 0.38/0.58          | ~ (l1_pre_topc @ X31)
% 0.38/0.58          | ~ (v2_pre_topc @ X31)
% 0.38/0.58          | (v2_struct_0 @ X31))),
% 0.38/0.58      inference('cnf', [status(esa)], [t30_connsp_2])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58        | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_B @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B) | (r2_hidden @ sk_F @ (k1_connsp_2 @ sk_B @ sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.38/0.58  thf('23', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('24', plain, ((r2_hidden @ sk_F @ (k1_connsp_2 @ sk_B @ sk_F))),
% 0.38/0.58      inference('clc', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf('25', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(redefinition_k6_domain_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X26 : $i, X27 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X26)
% 0.38/0.58          | ~ (m1_subset_1 @ X27 @ X26)
% 0.38/0.58          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F) = (k1_tarski @ sk_F))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      ((r2_hidden @ sk_G @ 
% 0.38/0.58        (k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58         sk_D_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(redefinition_k8_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.38/0.58          | ((k8_relset_1 @ X19 @ X20 @ X18 @ X21) = (k10_relat_1 @ X18 @ X21)))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58           sk_D_2 @ X0) = (k10_relat_1 @ sk_D_2 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      ((r2_hidden @ sk_G @ 
% 0.38/0.58        (k10_relat_1 @ sk_D_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['28', '31'])).
% 0.38/0.58  thf(d13_funct_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.58       ( ![B:$i,C:$i]:
% 0.38/0.58         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.38/0.58           ( ![D:$i]:
% 0.38/0.58             ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.58               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 0.38/0.58                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.58         (((X12) != (k10_relat_1 @ X11 @ X10))
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ X11 @ X13) @ X10)
% 0.38/0.58          | ~ (r2_hidden @ X13 @ X12)
% 0.38/0.58          | ~ (v1_funct_1 @ X11)
% 0.38/0.58          | ~ (v1_relat_1 @ X11))),
% 0.38/0.58      inference('cnf', [status(esa)], [d13_funct_1])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X11)
% 0.38/0.58          | ~ (v1_funct_1 @ X11)
% 0.38/0.58          | ~ (r2_hidden @ X13 @ (k10_relat_1 @ X11 @ X10))
% 0.38/0.58          | (r2_hidden @ (k1_funct_1 @ X11 @ X13) @ X10))),
% 0.38/0.58      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_G) @ 
% 0.38/0.58         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F))
% 0.38/0.58        | ~ (v1_funct_1 @ sk_D_2)
% 0.38/0.58        | ~ (v1_relat_1 @ sk_D_2))),
% 0.38/0.58      inference('sup-', [status(thm)], ['32', '34'])).
% 0.38/0.58  thf('36', plain, ((v1_funct_1 @ sk_D_2)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc1_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( v1_relat_1 @ C ) ))).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.58         ((v1_relat_1 @ X15)
% 0.38/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.58  thf('39', plain, ((v1_relat_1 @ sk_D_2)),
% 0.38/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_G) @ 
% 0.38/0.58        (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F))),
% 0.38/0.58      inference('demod', [status(thm)], ['35', '36', '39'])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      (((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_G) @ (k1_tarski @ sk_F))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['27', '40'])).
% 0.38/0.58  thf(d1_tarski, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (![X0 : $i, X3 : $i]:
% 0.38/0.58         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['42'])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | ((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['41', '43'])).
% 0.38/0.58  thf('45', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(dt_k1_connsp_2, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.58         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58       ( m1_subset_1 @
% 0.38/0.58         ( k1_connsp_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ X28)
% 0.38/0.58          | ~ (v2_pre_topc @ X28)
% 0.38/0.58          | (v2_struct_0 @ X28)
% 0.38/0.58          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.38/0.58          | (m1_subset_1 @ (k1_connsp_2 @ X28 @ X29) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_F) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.58  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_F) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.38/0.58  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      ((m1_subset_1 @ (k1_connsp_2 @ sk_B @ sk_F) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.58      inference('clc', [status(thm)], ['50', '51'])).
% 0.38/0.58  thf(t5_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.38/0.58          ( v1_xboole_0 @ C ) ) ))).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X6 @ X7)
% 0.38/0.58          | ~ (v1_xboole_0 @ X8)
% 0.38/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_B @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_B @ sk_F)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['44', '54'])).
% 0.38/0.58  thf('56', plain, (((k1_funct_1 @ sk_D_2 @ sk_G) = (sk_F))),
% 0.38/0.58      inference('sup-', [status(thm)], ['24', '55'])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            sk_D_2 @ sk_G) = (sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['16', '56'])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            sk_D_2 @ sk_G) = (sk_F)))),
% 0.38/0.58      inference('demod', [status(thm)], ['16', '56'])).
% 0.38/0.58  thf('59', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_E @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t52_tmap_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 0.38/0.58                 ( l1_pre_topc @ C ) ) =>
% 0.38/0.58               ( ![D:$i]:
% 0.38/0.58                 ( ( ( v1_funct_1 @ D ) & 
% 0.38/0.58                     ( v1_funct_2 @
% 0.38/0.58                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 0.38/0.58                     ( m1_subset_1 @
% 0.38/0.58                       D @ 
% 0.38/0.58                       ( k1_zfmisc_1 @
% 0.38/0.58                         ( k2_zfmisc_1 @
% 0.38/0.58                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.38/0.58                   ( ![E:$i]:
% 0.38/0.58                     ( ( ( v1_funct_1 @ E ) & 
% 0.38/0.58                         ( v1_funct_2 @
% 0.38/0.58                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.58                         ( m1_subset_1 @
% 0.38/0.58                           E @ 
% 0.38/0.58                           ( k1_zfmisc_1 @
% 0.38/0.58                             ( k2_zfmisc_1 @
% 0.38/0.58                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.58                       ( ![F:$i]:
% 0.38/0.58                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                           ( ![G:$i]:
% 0.38/0.58                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.38/0.58                               ( ( ( ( G ) =
% 0.38/0.58                                     ( k3_funct_2 @
% 0.38/0.58                                       ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                       ( u1_struct_0 @ C ) @ D @ F ) ) & 
% 0.38/0.58                                   ( r1_tmap_1 @ B @ C @ D @ F ) & 
% 0.38/0.58                                   ( r1_tmap_1 @ C @ A @ E @ G ) ) =>
% 0.38/0.58                                 ( r1_tmap_1 @
% 0.38/0.58                                   B @ A @ 
% 0.38/0.58                                   ( k1_partfun1 @
% 0.38/0.58                                     ( u1_struct_0 @ B ) @ 
% 0.38/0.58                                     ( u1_struct_0 @ C ) @ 
% 0.38/0.58                                     ( u1_struct_0 @ C ) @ 
% 0.38/0.58                                     ( u1_struct_0 @ A ) @ D @ E ) @ 
% 0.38/0.58                                   F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X36)
% 0.38/0.58          | ~ (v2_pre_topc @ X36)
% 0.38/0.58          | ~ (l1_pre_topc @ X36)
% 0.38/0.58          | ~ (v1_funct_1 @ X37)
% 0.38/0.58          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))
% 0.38/0.58          | ~ (m1_subset_1 @ X37 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))))
% 0.38/0.58          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 0.38/0.58          | ~ (r1_tmap_1 @ X36 @ X38 @ X37 @ X39)
% 0.38/0.58          | (r1_tmap_1 @ X36 @ X40 @ 
% 0.38/0.58             (k1_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38) @ 
% 0.38/0.58              (u1_struct_0 @ X38) @ (u1_struct_0 @ X40) @ X37 @ X41) @ 
% 0.38/0.58             X39)
% 0.38/0.58          | ((X42)
% 0.38/0.58              != (k3_funct_2 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38) @ 
% 0.38/0.58                  X37 @ X39))
% 0.38/0.58          | ~ (r1_tmap_1 @ X38 @ X40 @ X41 @ X42)
% 0.38/0.58          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X38))
% 0.38/0.58          | ~ (m1_subset_1 @ X41 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))))
% 0.38/0.58          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))
% 0.38/0.58          | ~ (v1_funct_1 @ X41)
% 0.38/0.58          | ~ (l1_pre_topc @ X38)
% 0.38/0.58          | ~ (v2_pre_topc @ X38)
% 0.38/0.58          | (v2_struct_0 @ X38)
% 0.38/0.58          | ~ (l1_pre_topc @ X40)
% 0.38/0.58          | ~ (v2_pre_topc @ X40)
% 0.38/0.58          | (v2_struct_0 @ X40))),
% 0.38/0.58      inference('cnf', [status(esa)], [t52_tmap_1])).
% 0.38/0.58  thf('61', plain,
% 0.38/0.58      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X40)
% 0.38/0.58          | ~ (v2_pre_topc @ X40)
% 0.38/0.58          | ~ (l1_pre_topc @ X40)
% 0.38/0.58          | (v2_struct_0 @ X38)
% 0.38/0.58          | ~ (v2_pre_topc @ X38)
% 0.38/0.58          | ~ (l1_pre_topc @ X38)
% 0.38/0.58          | ~ (v1_funct_1 @ X41)
% 0.38/0.58          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))
% 0.38/0.58          | ~ (m1_subset_1 @ X41 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))))
% 0.38/0.58          | ~ (m1_subset_1 @ 
% 0.38/0.58               (k3_funct_2 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38) @ X37 @ 
% 0.38/0.58                X39) @ 
% 0.38/0.58               (u1_struct_0 @ X38))
% 0.38/0.58          | ~ (r1_tmap_1 @ X38 @ X40 @ X41 @ 
% 0.38/0.58               (k3_funct_2 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38) @ X37 @ 
% 0.38/0.58                X39))
% 0.38/0.58          | (r1_tmap_1 @ X36 @ X40 @ 
% 0.38/0.58             (k1_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38) @ 
% 0.38/0.58              (u1_struct_0 @ X38) @ (u1_struct_0 @ X40) @ X37 @ X41) @ 
% 0.38/0.58             X39)
% 0.38/0.58          | ~ (r1_tmap_1 @ X36 @ X38 @ X37 @ X39)
% 0.38/0.58          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X36))
% 0.38/0.58          | ~ (m1_subset_1 @ X37 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))))
% 0.38/0.58          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))
% 0.38/0.58          | ~ (v1_funct_1 @ X37)
% 0.38/0.58          | ~ (l1_pre_topc @ X36)
% 0.38/0.58          | ~ (v2_pre_topc @ X36)
% 0.38/0.58          | (v2_struct_0 @ X36))),
% 0.38/0.58      inference('simplify', [status(thm)], ['60'])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X1)
% 0.38/0.58          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.58          | ~ (r1_tmap_1 @ X0 @ sk_B @ X1 @ X2)
% 0.38/0.58          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.58             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ sk_E) @ 
% 0.38/0.58             X2)
% 0.38/0.58          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ 
% 0.38/0.58               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.38/0.58                X2))
% 0.38/0.58          | ~ (m1_subset_1 @ 
% 0.38/0.58               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.38/0.58                X2) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.38/0.58          | ~ (v1_funct_1 @ sk_E)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58          | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['59', '61'])).
% 0.38/0.58  thf('63', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('64', plain, ((v1_funct_1 @ sk_E)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('66', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('69', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X0)
% 0.38/0.58          | ~ (v2_pre_topc @ X0)
% 0.38/0.58          | ~ (l1_pre_topc @ X0)
% 0.38/0.58          | ~ (v1_funct_1 @ X1)
% 0.38/0.58          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (m1_subset_1 @ X1 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.38/0.58          | ~ (r1_tmap_1 @ X0 @ sk_B @ X1 @ X2)
% 0.38/0.58          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.38/0.58             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ sk_E) @ 
% 0.38/0.58             X2)
% 0.38/0.58          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ 
% 0.38/0.58               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.38/0.58                X2))
% 0.38/0.58          | ~ (m1_subset_1 @ 
% 0.38/0.58               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 0.38/0.58                X2) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)],
% 0.38/0.58                ['62', '63', '64', '65', '66', '67', '68'])).
% 0.38/0.58  thf('70', plain,
% 0.38/0.58      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | ~ (m1_subset_1 @ 
% 0.38/0.58             (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58              sk_D_2 @ sk_G) @ 
% 0.38/0.58             (u1_struct_0 @ sk_B))
% 0.38/0.58        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.38/0.58           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.38/0.58           sk_G)
% 0.38/0.58        | ~ (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G)
% 0.38/0.58        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | ~ (m1_subset_1 @ sk_D_2 @ 
% 0.38/0.58             (k1_zfmisc_1 @ 
% 0.38/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))
% 0.38/0.58        | ~ (v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.58             (u1_struct_0 @ sk_B))
% 0.38/0.58        | ~ (v1_funct_1 @ sk_D_2)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_C_1)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_C_1)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['58', '69'])).
% 0.38/0.58  thf('71', plain, ((r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('72', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t49_tmap_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.38/0.58             ( l1_pre_topc @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.38/0.58                 ( m1_subset_1 @
% 0.38/0.58                   C @ 
% 0.38/0.58                   ( k1_zfmisc_1 @
% 0.38/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.38/0.58               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 0.38/0.58                 ( ![D:$i]:
% 0.38/0.58                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('74', plain,
% 0.38/0.58      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X32)
% 0.38/0.58          | ~ (v2_pre_topc @ X32)
% 0.38/0.58          | ~ (l1_pre_topc @ X32)
% 0.38/0.58          | ~ (v5_pre_topc @ X33 @ X32 @ X34)
% 0.38/0.58          | (r1_tmap_1 @ X32 @ X34 @ X33 @ X35)
% 0.38/0.58          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X32))
% 0.38/0.58          | ~ (m1_subset_1 @ X33 @ 
% 0.38/0.58               (k1_zfmisc_1 @ 
% 0.38/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X34))))
% 0.38/0.58          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X34))
% 0.38/0.58          | ~ (v1_funct_1 @ X33)
% 0.38/0.58          | ~ (l1_pre_topc @ X34)
% 0.38/0.58          | ~ (v2_pre_topc @ X34)
% 0.38/0.58          | (v2_struct_0 @ X34))),
% 0.38/0.58      inference('cnf', [status(esa)], [t49_tmap_1])).
% 0.38/0.58  thf('75', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.38/0.58          | ~ (v1_funct_1 @ sk_D_2)
% 0.38/0.58          | ~ (v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_B))
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0)
% 0.38/0.58          | ~ (v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B)
% 0.38/0.58          | ~ (l1_pre_topc @ sk_C_1)
% 0.38/0.58          | ~ (v2_pre_topc @ sk_C_1)
% 0.38/0.58          | (v2_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.58  thf('76', plain, ((v2_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('78', plain, ((v1_funct_1 @ sk_D_2)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('79', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('80', plain, ((v5_pre_topc @ sk_D_2 @ sk_C_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('81', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('82', plain, ((v2_pre_topc @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('83', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_B)
% 0.38/0.58          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ X0)
% 0.38/0.58          | (v2_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('demod', [status(thm)],
% 0.38/0.58                ['75', '76', '77', '78', '79', '80', '81', '82'])).
% 0.38/0.58  thf('84', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G)
% 0.38/0.58        | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['72', '83'])).
% 0.38/0.58  thf('85', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('86', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_B) | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G))),
% 0.38/0.58      inference('clc', [status(thm)], ['84', '85'])).
% 0.38/0.58  thf('87', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('88', plain, ((r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_2 @ sk_G)),
% 0.38/0.58      inference('clc', [status(thm)], ['86', '87'])).
% 0.38/0.58  thf('89', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('90', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_D_2 @ 
% 0.38/0.58        (k1_zfmisc_1 @ 
% 0.38/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('91', plain,
% 0.38/0.58      ((v1_funct_2 @ sk_D_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('92', plain, ((v1_funct_1 @ sk_D_2)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('93', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('94', plain, ((v2_pre_topc @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('95', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | ~ (m1_subset_1 @ 
% 0.38/0.58             (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58              sk_D_2 @ sk_G) @ 
% 0.38/0.58             (u1_struct_0 @ sk_B))
% 0.38/0.58        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.38/0.58           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.38/0.58           sk_G)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('demod', [status(thm)],
% 0.38/0.58                ['70', '71', '88', '89', '90', '91', '92', '93', '94'])).
% 0.38/0.58  thf('96', plain,
% 0.38/0.58      ((~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.38/0.58           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.38/0.58           sk_G)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['57', '95'])).
% 0.38/0.58  thf('97', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('98', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.38/0.58           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.38/0.58           sk_G)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('demod', [status(thm)], ['96', '97'])).
% 0.38/0.58  thf('99', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.38/0.58           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.38/0.58           sk_G)
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['98'])).
% 0.38/0.58  thf('100', plain,
% 0.38/0.58      (~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.38/0.58          (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.58           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_2 @ sk_E) @ 
% 0.38/0.58          sk_G)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('101', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | (v2_struct_0 @ sk_B)
% 0.38/0.58        | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['99', '100'])).
% 0.38/0.58  thf('102', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('103', plain,
% 0.38/0.58      (![X28 : $i, X29 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ X28)
% 0.38/0.58          | ~ (v2_pre_topc @ X28)
% 0.38/0.58          | (v2_struct_0 @ X28)
% 0.38/0.58          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.38/0.58          | (m1_subset_1 @ (k1_connsp_2 @ X28 @ X29) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_connsp_2])).
% 0.38/0.58  thf('104', plain,
% 0.38/0.58      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_G) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.58        | (v2_struct_0 @ sk_C_1)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_C_1)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_C_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['102', '103'])).
% 0.38/0.58  thf('105', plain, ((v2_pre_topc @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('106', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('107', plain,
% 0.38/0.58      (((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_G) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.58        | (v2_struct_0 @ sk_C_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.38/0.58  thf('108', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('109', plain,
% 0.38/0.58      ((m1_subset_1 @ (k1_connsp_2 @ sk_C_1 @ sk_G) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['107', '108'])).
% 0.38/0.58  thf('110', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X6 @ X7)
% 0.38/0.58          | ~ (v1_xboole_0 @ X8)
% 0.38/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t5_subset])).
% 0.38/0.58  thf('111', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C_1 @ sk_G)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['109', '110'])).
% 0.38/0.58  thf('112', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v2_struct_0 @ sk_A)
% 0.38/0.58          | (v2_struct_0 @ sk_B)
% 0.38/0.58          | (v2_struct_0 @ sk_C_1)
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (k1_connsp_2 @ sk_C_1 @ sk_G)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['101', '111'])).
% 0.38/0.58  thf('113', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['8', '112'])).
% 0.38/0.58  thf('114', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('115', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.38/0.58      inference('clc', [status(thm)], ['113', '114'])).
% 0.38/0.58  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('117', plain, ((v2_struct_0 @ sk_B)),
% 0.38/0.58      inference('clc', [status(thm)], ['115', '116'])).
% 0.38/0.58  thf('118', plain, ($false), inference('demod', [status(thm)], ['0', '117'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
