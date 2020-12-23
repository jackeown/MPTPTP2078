%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2HOFEIeSkJ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:35 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 239 expanded)
%              Number of leaves         :   39 (  89 expanded)
%              Depth                    :   24
%              Number of atoms          : 1686 (10362 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ X14 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X14 @ X15 @ X13 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_G ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ X18 )
      | ( ( k3_funct_2 @ X18 @ X19 @ X17 @ X20 )
        = ( k1_funct_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_G )
      = ( k1_funct_1 @ sk_D_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ X29 )
      | ( ( k6_domain_1 @ X29 @ X30 )
        = ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('19',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F )
      = ( k1_tarski @ sk_F ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_G @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_G @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ ( k1_tarski @ sk_F ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ! [E: $i] :
            ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) )
          <=> ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X22 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k8_relset_1 @ X23 @ X21 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t46_funct_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X1 ) @ X0 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X1 ) @ X0 )
      | ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_G ) @ ( k1_tarski @ sk_F ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_G )
      = sk_F ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ sk_G )
      = sk_F )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('35',plain,(
    ! [X27: $i] :
      ( ( l1_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ sk_G )
      = sk_F )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_G )
      = sk_F ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_G )
      = sk_F )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('44',plain,
    ( ( ( k1_funct_1 @ sk_D_1 @ sk_G )
      = sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_funct_1 @ sk_D_1 @ sk_G )
    = sk_F ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_G )
      = sk_F ) ),
    inference(demod,[status(thm)],['16','46'])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tmap_1 @ X35 @ X37 @ X36 @ X38 )
      | ( r1_tmap_1 @ X35 @ X39 @ ( k1_partfun1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ X36 @ X40 ) @ X38 )
      | ( X41
       != ( k3_funct_2 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) @ X36 @ X38 ) )
      | ~ ( r1_tmap_1 @ X37 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_tmap_1])).

thf('50',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) @ X36 @ X38 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( r1_tmap_1 @ X37 @ X39 @ X40 @ ( k3_funct_2 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) @ X36 @ X38 ) )
      | ( r1_tmap_1 @ X35 @ X39 @ ( k1_partfun1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X39 ) @ X36 @ X40 ) @ X38 )
      | ~ ( r1_tmap_1 @ X35 @ X37 @ X36 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
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
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
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
    inference(demod,[status(thm)],['51','52','53','54','55','56','57'])).

thf('59',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_G ) @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ sk_G )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','58'])).

thf('60',plain,(
    r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('63',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v5_pre_topc @ X32 @ X31 @ X33 )
      | ( r1_tmap_1 @ X31 @ X33 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t49_tmap_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ X0 )
      | ~ ( v5_pre_topc @ sk_D_1 @ sk_C_1 @ sk_B )
      | ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( v2_pre_topc @ sk_C_1 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v5_pre_topc @ sk_D_1 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','69','70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ sk_G ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ sk_G ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ sk_D_1 @ sk_G ) @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['59','60','77','78','79','80','81','82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_E ) @ sk_G )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k1_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D_1 @ sk_E ) @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X27: $i] :
      ( ( l1_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('93',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2HOFEIeSkJ
% 0.16/0.38  % Computer   : n010.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 09:26:30 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 1.06/1.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.28  % Solved by: fo/fo7.sh
% 1.06/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.28  % done 984 iterations in 0.783s
% 1.06/1.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.28  % SZS output start Refutation
% 1.06/1.28  thf(sk_F_type, type, sk_F: $i).
% 1.06/1.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.28  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.06/1.28  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.06/1.28  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.28  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.06/1.28  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 1.06/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.28  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.06/1.28  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.06/1.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.28  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.06/1.28  thf(sk_E_type, type, sk_E: $i).
% 1.06/1.28  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.28  thf(sk_G_type, type, sk_G: $i).
% 1.06/1.28  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 1.06/1.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.06/1.28  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.06/1.28  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.06/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.28  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.28  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.28  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.06/1.28  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.06/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.28  thf(t53_tmap_1, conjecture,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.28             ( l1_pre_topc @ B ) ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 1.06/1.28                 ( l1_pre_topc @ C ) ) =>
% 1.06/1.28               ( ![D:$i]:
% 1.06/1.28                 ( ( ( v1_funct_1 @ D ) & 
% 1.06/1.28                     ( v1_funct_2 @
% 1.06/1.28                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.28                     ( m1_subset_1 @
% 1.06/1.28                       D @ 
% 1.06/1.28                       ( k1_zfmisc_1 @
% 1.06/1.28                         ( k2_zfmisc_1 @
% 1.06/1.28                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.28                   ( ![E:$i]:
% 1.06/1.28                     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.28                         ( v1_funct_2 @
% 1.06/1.28                           E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.28                         ( m1_subset_1 @
% 1.06/1.28                           E @ 
% 1.06/1.28                           ( k1_zfmisc_1 @
% 1.06/1.28                             ( k2_zfmisc_1 @
% 1.06/1.28                               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.28                       ( ![F:$i]:
% 1.06/1.28                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.28                           ( ( ( v5_pre_topc @ D @ C @ B ) & 
% 1.06/1.28                               ( r1_tmap_1 @ B @ A @ E @ F ) ) =>
% 1.06/1.28                             ( ![G:$i]:
% 1.06/1.28                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.06/1.28                                 ( ( r2_hidden @
% 1.06/1.28                                     G @ 
% 1.06/1.28                                     ( k8_relset_1 @
% 1.06/1.28                                       ( u1_struct_0 @ C ) @ 
% 1.06/1.28                                       ( u1_struct_0 @ B ) @ D @ 
% 1.06/1.28                                       ( k6_domain_1 @ ( u1_struct_0 @ B ) @ F ) ) ) =>
% 1.06/1.28                                   ( r1_tmap_1 @
% 1.06/1.28                                     C @ A @ 
% 1.06/1.28                                     ( k1_partfun1 @
% 1.06/1.28                                       ( u1_struct_0 @ C ) @ 
% 1.06/1.28                                       ( u1_struct_0 @ B ) @ 
% 1.06/1.28                                       ( u1_struct_0 @ B ) @ 
% 1.06/1.28                                       ( u1_struct_0 @ A ) @ D @ E ) @ 
% 1.06/1.28                                     G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.28    (~( ![A:$i]:
% 1.06/1.28        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.06/1.28            ( l1_pre_topc @ A ) ) =>
% 1.06/1.28          ( ![B:$i]:
% 1.06/1.28            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.28                ( l1_pre_topc @ B ) ) =>
% 1.06/1.28              ( ![C:$i]:
% 1.06/1.28                ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 1.06/1.28                    ( l1_pre_topc @ C ) ) =>
% 1.06/1.28                  ( ![D:$i]:
% 1.06/1.28                    ( ( ( v1_funct_1 @ D ) & 
% 1.06/1.28                        ( v1_funct_2 @
% 1.06/1.28                          D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.06/1.28                        ( m1_subset_1 @
% 1.06/1.28                          D @ 
% 1.06/1.28                          ( k1_zfmisc_1 @
% 1.06/1.28                            ( k2_zfmisc_1 @
% 1.06/1.28                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.06/1.28                      ( ![E:$i]:
% 1.06/1.28                        ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.28                            ( v1_funct_2 @
% 1.06/1.28                              E @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.28                            ( m1_subset_1 @
% 1.06/1.28                              E @ 
% 1.06/1.28                              ( k1_zfmisc_1 @
% 1.06/1.28                                ( k2_zfmisc_1 @
% 1.06/1.28                                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.28                          ( ![F:$i]:
% 1.06/1.28                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.28                              ( ( ( v5_pre_topc @ D @ C @ B ) & 
% 1.06/1.28                                  ( r1_tmap_1 @ B @ A @ E @ F ) ) =>
% 1.06/1.28                                ( ![G:$i]:
% 1.06/1.28                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.06/1.28                                    ( ( r2_hidden @
% 1.06/1.28                                        G @ 
% 1.06/1.28                                        ( k8_relset_1 @
% 1.06/1.28                                          ( u1_struct_0 @ C ) @ 
% 1.06/1.28                                          ( u1_struct_0 @ B ) @ D @ 
% 1.06/1.28                                          ( k6_domain_1 @
% 1.06/1.28                                            ( u1_struct_0 @ B ) @ F ) ) ) =>
% 1.06/1.28                                      ( r1_tmap_1 @
% 1.06/1.28                                        C @ A @ 
% 1.06/1.28                                        ( k1_partfun1 @
% 1.06/1.28                                          ( u1_struct_0 @ C ) @ 
% 1.06/1.28                                          ( u1_struct_0 @ B ) @ 
% 1.06/1.28                                          ( u1_struct_0 @ B ) @ 
% 1.06/1.28                                          ( u1_struct_0 @ A ) @ D @ E ) @ 
% 1.06/1.28                                        G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.06/1.28    inference('cnf.neg', [status(esa)], [t53_tmap_1])).
% 1.06/1.28  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('2', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_D_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(dt_k3_funct_2, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.28     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.06/1.28         ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.28         ( m1_subset_1 @ D @ A ) ) =>
% 1.06/1.28       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 1.06/1.28  thf('3', plain,
% 1.06/1.28      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 1.06/1.28          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 1.06/1.28          | ~ (v1_funct_1 @ X13)
% 1.06/1.28          | (v1_xboole_0 @ X14)
% 1.06/1.28          | ~ (m1_subset_1 @ X16 @ X14)
% 1.06/1.28          | (m1_subset_1 @ (k3_funct_2 @ X14 @ X15 @ X13 @ X16) @ X15))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 1.06/1.28  thf('4', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((m1_subset_1 @ 
% 1.06/1.28           (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            sk_D_1 @ X0) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28          | ~ (v1_funct_1 @ sk_D_1)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ 
% 1.06/1.28               (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.28  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('6', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('7', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((m1_subset_1 @ 
% 1.06/1.28           (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            sk_D_1 @ X0) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 1.06/1.28      inference('demod', [status(thm)], ['4', '5', '6'])).
% 1.06/1.28  thf('8', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28        | (m1_subset_1 @ 
% 1.06/1.28           (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            sk_D_1 @ sk_G) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['1', '7'])).
% 1.06/1.28  thf('9', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('10', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_D_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(redefinition_k3_funct_2, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.28     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.06/1.28         ( v1_funct_2 @ C @ A @ B ) & 
% 1.06/1.28         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.06/1.28         ( m1_subset_1 @ D @ A ) ) =>
% 1.06/1.28       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.06/1.28  thf('11', plain,
% 1.06/1.28      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.06/1.28         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.06/1.28          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 1.06/1.28          | ~ (v1_funct_1 @ X17)
% 1.06/1.28          | (v1_xboole_0 @ X18)
% 1.06/1.28          | ~ (m1_subset_1 @ X20 @ X18)
% 1.06/1.28          | ((k3_funct_2 @ X18 @ X19 @ X17 @ X20) = (k1_funct_1 @ X17 @ X20)))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.06/1.28  thf('12', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            sk_D_1 @ X0) = (k1_funct_1 @ sk_D_1 @ X0))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28          | ~ (v1_funct_1 @ sk_D_1)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ 
% 1.06/1.28               (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['10', '11'])).
% 1.06/1.28  thf('13', plain, ((v1_funct_1 @ sk_D_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('14', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('15', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         (((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            sk_D_1 @ X0) = (k1_funct_1 @ sk_D_1 @ X0))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28          | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 1.06/1.28      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.06/1.28  thf('16', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            sk_D_1 @ sk_G) = (k1_funct_1 @ sk_D_1 @ sk_G)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['9', '15'])).
% 1.06/1.28  thf('17', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_B))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(redefinition_k6_domain_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.06/1.28       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.06/1.28  thf('18', plain,
% 1.06/1.28      (![X29 : $i, X30 : $i]:
% 1.06/1.28         ((v1_xboole_0 @ X29)
% 1.06/1.28          | ~ (m1_subset_1 @ X30 @ X29)
% 1.06/1.28          | ((k6_domain_1 @ X29 @ X30) = (k1_tarski @ X30)))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.06/1.28  thf('19', plain,
% 1.06/1.28      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F) = (k1_tarski @ sk_F))
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['17', '18'])).
% 1.06/1.28  thf('20', plain,
% 1.06/1.28      ((r2_hidden @ sk_G @ 
% 1.06/1.28        (k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28         sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_F)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('21', plain,
% 1.06/1.28      (((r2_hidden @ sk_G @ 
% 1.06/1.28         (k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28          sk_D_1 @ (k1_tarski @ sk_F)))
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.06/1.28      inference('sup+', [status(thm)], ['19', '20'])).
% 1.06/1.28  thf('22', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_D_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t46_funct_2, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.28     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.06/1.28         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.06/1.28       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.06/1.28         ( ![E:$i]:
% 1.06/1.28           ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ B @ D @ C ) ) <=>
% 1.06/1.28             ( ( r2_hidden @ E @ A ) & 
% 1.06/1.28               ( r2_hidden @ ( k1_funct_1 @ D @ E ) @ C ) ) ) ) ) ))).
% 1.06/1.28  thf('23', plain,
% 1.06/1.28      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.28         (((X21) = (k1_xboole_0))
% 1.06/1.28          | ~ (v1_funct_1 @ X22)
% 1.06/1.28          | ~ (v1_funct_2 @ X22 @ X23 @ X21)
% 1.06/1.28          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 1.06/1.28          | (r2_hidden @ (k1_funct_1 @ X22 @ X24) @ X25)
% 1.06/1.28          | ~ (r2_hidden @ X24 @ (k8_relset_1 @ X23 @ X21 @ X22 @ X25)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t46_funct_2])).
% 1.06/1.28  thf('24', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X1 @ 
% 1.06/1.28             (k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28              sk_D_1 @ X0))
% 1.06/1.28          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X1) @ X0)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ 
% 1.06/1.28               (u1_struct_0 @ sk_B))
% 1.06/1.28          | ~ (v1_funct_1 @ sk_D_1)
% 1.06/1.28          | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['22', '23'])).
% 1.06/1.28  thf('25', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('26', plain, ((v1_funct_1 @ sk_D_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('27', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X1 @ 
% 1.06/1.28             (k8_relset_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28              sk_D_1 @ X0))
% 1.06/1.28          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ X1) @ X0)
% 1.06/1.28          | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 1.06/1.28      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.06/1.28  thf('28', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.06/1.28        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_G) @ (k1_tarski @ sk_F)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['21', '27'])).
% 1.06/1.28  thf(d1_tarski, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.06/1.28       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.06/1.28  thf('29', plain,
% 1.06/1.28      (![X0 : $i, X2 : $i, X3 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d1_tarski])).
% 1.06/1.28  thf('30', plain,
% 1.06/1.28      (![X0 : $i, X3 : $i]:
% 1.06/1.28         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['29'])).
% 1.06/1.28  thf('31', plain,
% 1.06/1.28      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.06/1.28        | ((k1_funct_1 @ sk_D_1 @ sk_G) = (sk_F)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['28', '30'])).
% 1.06/1.28  thf(fc2_struct_0, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.06/1.28       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.28  thf('32', plain,
% 1.06/1.28      (![X28 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 1.06/1.28          | ~ (l1_struct_0 @ X28)
% 1.06/1.28          | (v2_struct_0 @ X28))),
% 1.06/1.28      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.06/1.28  thf('33', plain,
% 1.06/1.28      ((((k1_funct_1 @ sk_D_1 @ sk_G) = (sk_F))
% 1.06/1.28        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | ~ (l1_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['31', '32'])).
% 1.06/1.28  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(dt_l1_pre_topc, axiom,
% 1.06/1.28    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.06/1.28  thf('35', plain,
% 1.06/1.28      (![X27 : $i]: ((l1_struct_0 @ X27) | ~ (l1_pre_topc @ X27))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.28  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['34', '35'])).
% 1.06/1.28  thf('37', plain,
% 1.06/1.28      ((((k1_funct_1 @ sk_D_1 @ sk_G) = (sk_F))
% 1.06/1.28        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['33', '36'])).
% 1.06/1.28  thf('38', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('39', plain,
% 1.06/1.28      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.06/1.28        | ((k1_funct_1 @ sk_D_1 @ sk_G) = (sk_F)))),
% 1.06/1.28      inference('clc', [status(thm)], ['37', '38'])).
% 1.06/1.28  thf('40', plain,
% 1.06/1.28      (![X28 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 1.06/1.28          | ~ (l1_struct_0 @ X28)
% 1.06/1.28          | (v2_struct_0 @ X28))),
% 1.06/1.28      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.06/1.28  thf('41', plain,
% 1.06/1.28      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.06/1.28        | ((k1_funct_1 @ sk_D_1 @ sk_G) = (sk_F))
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | ~ (l1_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['39', '40'])).
% 1.06/1.28  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.06/1.28  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.28      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.28  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['34', '35'])).
% 1.06/1.28  thf('44', plain,
% 1.06/1.28      ((((k1_funct_1 @ sk_D_1 @ sk_G) = (sk_F)) | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['41', '42', '43'])).
% 1.06/1.28  thf('45', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('46', plain, (((k1_funct_1 @ sk_D_1 @ sk_G) = (sk_F))),
% 1.06/1.28      inference('clc', [status(thm)], ['44', '45'])).
% 1.06/1.28  thf('47', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28        | ((k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            sk_D_1 @ sk_G) = (sk_F)))),
% 1.06/1.28      inference('demod', [status(thm)], ['16', '46'])).
% 1.06/1.28  thf('48', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_E @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t52_tmap_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.28             ( l1_pre_topc @ B ) ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( ( ~( v2_struct_0 @ C ) ) & ( v2_pre_topc @ C ) & 
% 1.06/1.28                 ( l1_pre_topc @ C ) ) =>
% 1.06/1.28               ( ![D:$i]:
% 1.06/1.28                 ( ( ( v1_funct_1 @ D ) & 
% 1.06/1.28                     ( v1_funct_2 @
% 1.06/1.28                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) & 
% 1.06/1.28                     ( m1_subset_1 @
% 1.06/1.28                       D @ 
% 1.06/1.28                       ( k1_zfmisc_1 @
% 1.06/1.28                         ( k2_zfmisc_1 @
% 1.06/1.28                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 1.06/1.28                   ( ![E:$i]:
% 1.06/1.28                     ( ( ( v1_funct_1 @ E ) & 
% 1.06/1.28                         ( v1_funct_2 @
% 1.06/1.28                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.28                         ( m1_subset_1 @
% 1.06/1.28                           E @ 
% 1.06/1.28                           ( k1_zfmisc_1 @
% 1.06/1.28                             ( k2_zfmisc_1 @
% 1.06/1.28                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.28                       ( ![F:$i]:
% 1.06/1.28                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.28                           ( ![G:$i]:
% 1.06/1.28                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 1.06/1.28                               ( ( ( ( G ) =
% 1.06/1.28                                     ( k3_funct_2 @
% 1.06/1.28                                       ( u1_struct_0 @ B ) @ 
% 1.06/1.28                                       ( u1_struct_0 @ C ) @ D @ F ) ) & 
% 1.06/1.28                                   ( r1_tmap_1 @ B @ C @ D @ F ) & 
% 1.06/1.28                                   ( r1_tmap_1 @ C @ A @ E @ G ) ) =>
% 1.06/1.28                                 ( r1_tmap_1 @
% 1.06/1.28                                   B @ A @ 
% 1.06/1.28                                   ( k1_partfun1 @
% 1.06/1.28                                     ( u1_struct_0 @ B ) @ 
% 1.06/1.28                                     ( u1_struct_0 @ C ) @ 
% 1.06/1.28                                     ( u1_struct_0 @ C ) @ 
% 1.06/1.28                                     ( u1_struct_0 @ A ) @ D @ E ) @ 
% 1.06/1.28                                   F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.28  thf('49', plain,
% 1.06/1.28      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X35)
% 1.06/1.28          | ~ (v2_pre_topc @ X35)
% 1.06/1.28          | ~ (l1_pre_topc @ X35)
% 1.06/1.28          | ~ (v1_funct_1 @ X36)
% 1.06/1.28          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))
% 1.06/1.28          | ~ (m1_subset_1 @ X36 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))))
% 1.06/1.28          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X35))
% 1.06/1.28          | ~ (r1_tmap_1 @ X35 @ X37 @ X36 @ X38)
% 1.06/1.28          | (r1_tmap_1 @ X35 @ X39 @ 
% 1.06/1.28             (k1_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37) @ 
% 1.06/1.28              (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ X36 @ X40) @ 
% 1.06/1.28             X38)
% 1.06/1.28          | ((X41)
% 1.06/1.28              != (k3_funct_2 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37) @ 
% 1.06/1.28                  X36 @ X38))
% 1.06/1.28          | ~ (r1_tmap_1 @ X37 @ X39 @ X40 @ X41)
% 1.06/1.28          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X37))
% 1.06/1.28          | ~ (m1_subset_1 @ X40 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 1.06/1.28          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 1.06/1.28          | ~ (v1_funct_1 @ X40)
% 1.06/1.28          | ~ (l1_pre_topc @ X37)
% 1.06/1.28          | ~ (v2_pre_topc @ X37)
% 1.06/1.28          | (v2_struct_0 @ X37)
% 1.06/1.28          | ~ (l1_pre_topc @ X39)
% 1.06/1.28          | ~ (v2_pre_topc @ X39)
% 1.06/1.28          | (v2_struct_0 @ X39))),
% 1.06/1.28      inference('cnf', [status(esa)], [t52_tmap_1])).
% 1.06/1.28  thf('50', plain,
% 1.06/1.28      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X39)
% 1.06/1.28          | ~ (v2_pre_topc @ X39)
% 1.06/1.28          | ~ (l1_pre_topc @ X39)
% 1.06/1.28          | (v2_struct_0 @ X37)
% 1.06/1.28          | ~ (v2_pre_topc @ X37)
% 1.06/1.28          | ~ (l1_pre_topc @ X37)
% 1.06/1.28          | ~ (v1_funct_1 @ X40)
% 1.06/1.28          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))
% 1.06/1.28          | ~ (m1_subset_1 @ X40 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X39))))
% 1.06/1.28          | ~ (m1_subset_1 @ 
% 1.06/1.28               (k3_funct_2 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37) @ X36 @ 
% 1.06/1.28                X38) @ 
% 1.06/1.28               (u1_struct_0 @ X37))
% 1.06/1.28          | ~ (r1_tmap_1 @ X37 @ X39 @ X40 @ 
% 1.06/1.28               (k3_funct_2 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37) @ X36 @ 
% 1.06/1.28                X38))
% 1.06/1.28          | (r1_tmap_1 @ X35 @ X39 @ 
% 1.06/1.28             (k1_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37) @ 
% 1.06/1.28              (u1_struct_0 @ X37) @ (u1_struct_0 @ X39) @ X36 @ X40) @ 
% 1.06/1.28             X38)
% 1.06/1.28          | ~ (r1_tmap_1 @ X35 @ X37 @ X36 @ X38)
% 1.06/1.28          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X35))
% 1.06/1.28          | ~ (m1_subset_1 @ X36 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))))
% 1.06/1.28          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X37))
% 1.06/1.28          | ~ (v1_funct_1 @ X36)
% 1.06/1.28          | ~ (l1_pre_topc @ X35)
% 1.06/1.28          | ~ (v2_pre_topc @ X35)
% 1.06/1.28          | (v2_struct_0 @ X35))),
% 1.06/1.28      inference('simplify', [status(thm)], ['49'])).
% 1.06/1.28  thf('51', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v1_funct_1 @ X1)
% 1.06/1.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.28          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.06/1.28          | ~ (r1_tmap_1 @ X0 @ sk_B @ X1 @ X2)
% 1.06/1.28          | (r1_tmap_1 @ X0 @ sk_A @ 
% 1.06/1.28             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ sk_E) @ 
% 1.06/1.28             X2)
% 1.06/1.28          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ 
% 1.06/1.28               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 1.06/1.28                X2))
% 1.06/1.28          | ~ (m1_subset_1 @ 
% 1.06/1.28               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 1.06/1.28                X2) @ 
% 1.06/1.28               (u1_struct_0 @ sk_B))
% 1.06/1.28          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.06/1.28          | ~ (v1_funct_1 @ sk_E)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.28          | (v2_struct_0 @ sk_B)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_A)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_A)
% 1.06/1.28          | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['48', '50'])).
% 1.06/1.28  thf('52', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('53', plain, ((v1_funct_1 @ sk_E)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('54', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('55', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('58', plain,
% 1.06/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X0)
% 1.06/1.28          | ~ (v2_pre_topc @ X0)
% 1.06/1.28          | ~ (l1_pre_topc @ X0)
% 1.06/1.28          | ~ (v1_funct_1 @ X1)
% 1.06/1.28          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.06/1.28          | ~ (m1_subset_1 @ X1 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.06/1.28          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.06/1.28          | ~ (r1_tmap_1 @ X0 @ sk_B @ X1 @ X2)
% 1.06/1.28          | (r1_tmap_1 @ X0 @ sk_A @ 
% 1.06/1.28             (k1_partfun1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28              (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ sk_E) @ 
% 1.06/1.28             X2)
% 1.06/1.28          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ 
% 1.06/1.28               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 1.06/1.28                X2))
% 1.06/1.28          | ~ (m1_subset_1 @ 
% 1.06/1.28               (k3_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ X1 @ 
% 1.06/1.28                X2) @ 
% 1.06/1.28               (u1_struct_0 @ sk_B))
% 1.06/1.28          | (v2_struct_0 @ sk_B)
% 1.06/1.28          | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('demod', [status(thm)],
% 1.06/1.28                ['51', '52', '53', '54', '55', '56', '57'])).
% 1.06/1.28  thf('59', plain,
% 1.06/1.28      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F)
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | ~ (m1_subset_1 @ 
% 1.06/1.28             (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28              sk_D_1 @ sk_G) @ 
% 1.06/1.28             (u1_struct_0 @ sk_B))
% 1.06/1.28        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 1.06/1.28           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_1 @ sk_E) @ 
% 1.06/1.28           sk_G)
% 1.06/1.28        | ~ (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ sk_G)
% 1.06/1.28        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28        | ~ (m1_subset_1 @ sk_D_1 @ 
% 1.06/1.28             (k1_zfmisc_1 @ 
% 1.06/1.28              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))
% 1.06/1.28        | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ 
% 1.06/1.28             (u1_struct_0 @ sk_B))
% 1.06/1.28        | ~ (v1_funct_1 @ sk_D_1)
% 1.06/1.28        | ~ (l1_pre_topc @ sk_C_1)
% 1.06/1.28        | ~ (v2_pre_topc @ sk_C_1)
% 1.06/1.28        | (v2_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['47', '58'])).
% 1.06/1.28  thf('60', plain, ((r1_tmap_1 @ sk_B @ sk_A @ sk_E @ sk_F)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('61', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('62', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_D_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(t49_tmap_1, axiom,
% 1.06/1.28    (![A:$i]:
% 1.06/1.28     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.28       ( ![B:$i]:
% 1.06/1.28         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.06/1.28             ( l1_pre_topc @ B ) ) =>
% 1.06/1.28           ( ![C:$i]:
% 1.06/1.28             ( ( ( v1_funct_1 @ C ) & 
% 1.06/1.28                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 1.06/1.28                 ( m1_subset_1 @
% 1.06/1.28                   C @ 
% 1.06/1.28                   ( k1_zfmisc_1 @
% 1.06/1.28                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.06/1.28               ( ( v5_pre_topc @ C @ B @ A ) <=>
% 1.06/1.28                 ( ![D:$i]:
% 1.06/1.28                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.28                     ( r1_tmap_1 @ B @ A @ C @ D ) ) ) ) ) ) ) ) ))).
% 1.06/1.28  thf('63', plain,
% 1.06/1.28      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.06/1.28         ((v2_struct_0 @ X31)
% 1.06/1.28          | ~ (v2_pre_topc @ X31)
% 1.06/1.28          | ~ (l1_pre_topc @ X31)
% 1.06/1.28          | ~ (v5_pre_topc @ X32 @ X31 @ X33)
% 1.06/1.28          | (r1_tmap_1 @ X31 @ X33 @ X32 @ X34)
% 1.06/1.28          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X31))
% 1.06/1.28          | ~ (m1_subset_1 @ X32 @ 
% 1.06/1.28               (k1_zfmisc_1 @ 
% 1.06/1.28                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X33))))
% 1.06/1.28          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X33))
% 1.06/1.28          | ~ (v1_funct_1 @ X32)
% 1.06/1.28          | ~ (l1_pre_topc @ X33)
% 1.06/1.28          | ~ (v2_pre_topc @ X33)
% 1.06/1.28          | (v2_struct_0 @ X33))),
% 1.06/1.28      inference('cnf', [status(esa)], [t49_tmap_1])).
% 1.06/1.28  thf('64', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_B)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_B)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_B)
% 1.06/1.28          | ~ (v1_funct_1 @ sk_D_1)
% 1.06/1.28          | ~ (v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ 
% 1.06/1.28               (u1_struct_0 @ sk_B))
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28          | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ X0)
% 1.06/1.28          | ~ (v5_pre_topc @ sk_D_1 @ sk_C_1 @ sk_B)
% 1.06/1.28          | ~ (l1_pre_topc @ sk_C_1)
% 1.06/1.28          | ~ (v2_pre_topc @ sk_C_1)
% 1.06/1.28          | (v2_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['62', '63'])).
% 1.06/1.28  thf('65', plain, ((v2_pre_topc @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('67', plain, ((v1_funct_1 @ sk_D_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('68', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('69', plain, ((v5_pre_topc @ sk_D_1 @ sk_C_1 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('70', plain, ((l1_pre_topc @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('71', plain, ((v2_pre_topc @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('72', plain,
% 1.06/1.28      (![X0 : $i]:
% 1.06/1.28         ((v2_struct_0 @ sk_B)
% 1.06/1.28          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28          | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ X0)
% 1.06/1.28          | (v2_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)],
% 1.06/1.28                ['64', '65', '66', '67', '68', '69', '70', '71'])).
% 1.06/1.28  thf('73', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_C_1)
% 1.06/1.28        | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ sk_G)
% 1.06/1.28        | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['61', '72'])).
% 1.06/1.28  thf('74', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('75', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_B) | (r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ sk_G))),
% 1.06/1.28      inference('clc', [status(thm)], ['73', '74'])).
% 1.06/1.28  thf('76', plain, (~ (v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('77', plain, ((r1_tmap_1 @ sk_C_1 @ sk_B @ sk_D_1 @ sk_G)),
% 1.06/1.28      inference('clc', [status(thm)], ['75', '76'])).
% 1.06/1.28  thf('78', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('79', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_D_1 @ 
% 1.06/1.28        (k1_zfmisc_1 @ 
% 1.06/1.28         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('80', plain,
% 1.06/1.28      ((v1_funct_2 @ sk_D_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('81', plain, ((v1_funct_1 @ sk_D_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('82', plain, ((l1_pre_topc @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('83', plain, ((v2_pre_topc @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('84', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | ~ (m1_subset_1 @ 
% 1.06/1.28             (k3_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28              sk_D_1 @ sk_G) @ 
% 1.06/1.28             (u1_struct_0 @ sk_B))
% 1.06/1.28        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 1.06/1.28           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_1 @ sk_E) @ 
% 1.06/1.28           sk_G)
% 1.06/1.28        | (v2_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)],
% 1.06/1.28                ['59', '60', '77', '78', '79', '80', '81', '82', '83'])).
% 1.06/1.28  thf('85', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28        | (v2_struct_0 @ sk_C_1)
% 1.06/1.28        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 1.06/1.28           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_1 @ sk_E) @ 
% 1.06/1.28           sk_G)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A)
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 1.06/1.28      inference('sup-', [status(thm)], ['8', '84'])).
% 1.06/1.28  thf('86', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 1.06/1.28           (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28            (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_1 @ sk_E) @ 
% 1.06/1.28           sk_G)
% 1.06/1.28        | (v2_struct_0 @ sk_C_1)
% 1.06/1.28        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['85'])).
% 1.06/1.28  thf('87', plain,
% 1.06/1.28      (~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 1.06/1.28          (k1_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B) @ 
% 1.06/1.28           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D_1 @ sk_E) @ 
% 1.06/1.28          sk_G)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('88', plain,
% 1.06/1.28      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 1.06/1.28        | (v2_struct_0 @ sk_C_1)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('sup-', [status(thm)], ['86', '87'])).
% 1.06/1.28  thf('89', plain,
% 1.06/1.28      (![X28 : $i]:
% 1.06/1.28         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 1.06/1.28          | ~ (l1_struct_0 @ X28)
% 1.06/1.28          | (v2_struct_0 @ X28))),
% 1.06/1.28      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.06/1.28  thf('90', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_C_1)
% 1.06/1.28        | (v2_struct_0 @ sk_C_1)
% 1.06/1.28        | ~ (l1_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('sup-', [status(thm)], ['88', '89'])).
% 1.06/1.28  thf('91', plain, ((l1_pre_topc @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('92', plain,
% 1.06/1.28      (![X27 : $i]: ((l1_struct_0 @ X27) | ~ (l1_pre_topc @ X27))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.28  thf('93', plain, ((l1_struct_0 @ sk_C_1)),
% 1.06/1.28      inference('sup-', [status(thm)], ['91', '92'])).
% 1.06/1.28  thf('94', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_A)
% 1.06/1.28        | (v2_struct_0 @ sk_B)
% 1.06/1.28        | (v2_struct_0 @ sk_C_1)
% 1.06/1.28        | (v2_struct_0 @ sk_C_1))),
% 1.06/1.28      inference('demod', [status(thm)], ['90', '93'])).
% 1.06/1.28  thf('95', plain,
% 1.06/1.28      (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 1.06/1.28      inference('simplify', [status(thm)], ['94'])).
% 1.06/1.28  thf('96', plain, (~ (v2_struct_0 @ sk_C_1)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('97', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 1.06/1.28      inference('clc', [status(thm)], ['95', '96'])).
% 1.06/1.28  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('99', plain, ((v2_struct_0 @ sk_B)),
% 1.06/1.28      inference('clc', [status(thm)], ['97', '98'])).
% 1.06/1.28  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 1.06/1.28  
% 1.06/1.28  % SZS output end Refutation
% 1.06/1.28  
% 1.06/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
