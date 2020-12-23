%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rjl5XMq8Vs

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:47 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 242 expanded)
%              Number of leaves         :   37 (  88 expanded)
%              Depth                    :   19
%              Number of atoms          : 1116 (6817 expanded)
%              Number of equality atoms :   35 ( 204 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(t77_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                            = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v3_borsuk_1 @ C @ A @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                     => ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( D = E )
                           => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                              = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('13',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t76_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                            = ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v4_tex_2 @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v3_borsuk_1 @ X20 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( X21 != X22 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) @ X20 @ X21 )
        = ( k2_pre_topc @ X19 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v5_pre_topc @ X20 @ X19 @ X18 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v3_tdlat_3 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( v3_tdlat_3 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v5_pre_topc @ X20 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) @ X20 @ X22 )
        = ( k2_pre_topc @ X19 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_borsuk_1 @ X20 @ X19 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v4_tex_2 @ X18 @ X19 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( ( k8_relset_1 @ X4 @ X5 @ X3 @ X6 )
        = ( k10_relat_1 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k10_relat_1 @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','28','29','30','31','32','33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k10_relat_1 @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( k10_relat_1 @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('43',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k10_relat_1 @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k10_relat_1 @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('48',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('49',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('54',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k10_relat_1 @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k10_relat_1 @ sk_C @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['61','62'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('65',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('75',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['67','72','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_xboole_0 @ ( sk_B @ sk_B_1 ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('85',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71'])).

thf('86',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rjl5XMq8Vs
% 0.15/0.37  % Computer   : n001.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:52:45 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.56  % Solved by: fo/fo7.sh
% 0.23/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.56  % done 85 iterations in 0.064s
% 0.23/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.56  % SZS output start Refutation
% 0.23/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.23/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.56  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.23/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.56  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.23/0.56  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.23/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.23/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.56  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.23/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.23/0.56  thf(t77_tex_2, conjecture,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.23/0.56         ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.23/0.56             ( m1_pre_topc @ B @ A ) ) =>
% 0.23/0.56           ( ![C:$i]:
% 0.23/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.23/0.56                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.23/0.56                 ( m1_subset_1 @
% 0.23/0.56                   C @ 
% 0.23/0.56                   ( k1_zfmisc_1 @
% 0.23/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.23/0.56               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.23/0.56                 ( ![D:$i]:
% 0.23/0.56                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.23/0.56                     ( ![E:$i]:
% 0.23/0.56                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.56                         ( ( ( D ) = ( E ) ) =>
% 0.23/0.56                           ( ( k8_relset_1 @
% 0.23/0.56                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.23/0.56                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.23/0.56                             ( k2_pre_topc @
% 0.23/0.56                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.56    (~( ![A:$i]:
% 0.23/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.56            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56          ( ![B:$i]:
% 0.23/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.23/0.56                ( m1_pre_topc @ B @ A ) ) =>
% 0.23/0.56              ( ![C:$i]:
% 0.23/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.56                    ( v1_funct_2 @
% 0.23/0.56                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.23/0.56                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.23/0.56                    ( m1_subset_1 @
% 0.23/0.56                      C @ 
% 0.23/0.56                      ( k1_zfmisc_1 @
% 0.23/0.56                        ( k2_zfmisc_1 @
% 0.23/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.23/0.56                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.23/0.56                    ( ![D:$i]:
% 0.23/0.56                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.23/0.56                        ( ![E:$i]:
% 0.23/0.56                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.56                            ( ( ( D ) = ( E ) ) =>
% 0.23/0.56                              ( ( k8_relset_1 @
% 0.23/0.56                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.23/0.56                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.23/0.56                                ( k2_pre_topc @
% 0.23/0.56                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.56    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.23/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('1', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('2', plain, (((sk_D) = (sk_E))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.23/0.56  thf('4', plain,
% 0.23/0.56      (![X14 : $i, X15 : $i]:
% 0.23/0.56         ((v1_xboole_0 @ X14)
% 0.23/0.56          | ~ (m1_subset_1 @ X15 @ X14)
% 0.23/0.56          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.23/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.56  thf('5', plain,
% 0.23/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.56  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.23/0.56  thf(dt_k6_domain_1, axiom,
% 0.23/0.56    (![A:$i,B:$i]:
% 0.23/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.23/0.56       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.56  thf('7', plain,
% 0.23/0.56      (![X12 : $i, X13 : $i]:
% 0.23/0.56         ((v1_xboole_0 @ X12)
% 0.23/0.56          | ~ (m1_subset_1 @ X13 @ X12)
% 0.23/0.56          | (m1_subset_1 @ (k6_domain_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12)))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.23/0.56  thf('8', plain,
% 0.23/0.56      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.23/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.56  thf('9', plain,
% 0.23/0.56      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('sup+', [status(thm)], ['5', '8'])).
% 0.23/0.56  thf('10', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.23/0.56  thf('11', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('12', plain,
% 0.23/0.56      (![X14 : $i, X15 : $i]:
% 0.23/0.56         ((v1_xboole_0 @ X14)
% 0.23/0.56          | ~ (m1_subset_1 @ X15 @ X14)
% 0.23/0.56          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.23/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.23/0.56  thf('13', plain,
% 0.23/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.56  thf('14', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('15', plain,
% 0.23/0.56      (![X12 : $i, X13 : $i]:
% 0.23/0.56         ((v1_xboole_0 @ X12)
% 0.23/0.56          | ~ (m1_subset_1 @ X13 @ X12)
% 0.23/0.56          | (m1_subset_1 @ (k6_domain_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12)))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.23/0.56  thf('16', plain,
% 0.23/0.56      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.23/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.56  thf('17', plain,
% 0.23/0.56      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup+', [status(thm)], ['13', '16'])).
% 0.23/0.56  thf('18', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.23/0.56        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.23/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.23/0.56  thf('19', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_C @ 
% 0.23/0.56        (k1_zfmisc_1 @ 
% 0.23/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(t76_tex_2, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.23/0.56         ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.23/0.56             ( m1_pre_topc @ B @ A ) ) =>
% 0.23/0.56           ( ![C:$i]:
% 0.23/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.23/0.56                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.23/0.56                 ( m1_subset_1 @
% 0.23/0.56                   C @ 
% 0.23/0.56                   ( k1_zfmisc_1 @
% 0.23/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.23/0.56               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.23/0.56                 ( ![D:$i]:
% 0.23/0.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.23/0.56                     ( ![E:$i]:
% 0.23/0.56                       ( ( m1_subset_1 @
% 0.23/0.56                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.56                         ( ( ( D ) = ( E ) ) =>
% 0.23/0.56                           ( ( k8_relset_1 @
% 0.23/0.56                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.23/0.56                               D ) =
% 0.23/0.56                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.56  thf('20', plain,
% 0.23/0.56      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.56         ((v2_struct_0 @ X18)
% 0.23/0.56          | ~ (v4_tex_2 @ X18 @ X19)
% 0.23/0.56          | ~ (m1_pre_topc @ X18 @ X19)
% 0.23/0.56          | ~ (v3_borsuk_1 @ X20 @ X19 @ X18)
% 0.23/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.23/0.56          | ((X21) != (X22))
% 0.23/0.56          | ((k8_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18) @ X20 @ 
% 0.23/0.56              X21) = (k2_pre_topc @ X19 @ X22))
% 0.23/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.23/0.56          | ~ (m1_subset_1 @ X20 @ 
% 0.23/0.56               (k1_zfmisc_1 @ 
% 0.23/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))))
% 0.23/0.56          | ~ (v5_pre_topc @ X20 @ X19 @ X18)
% 0.23/0.56          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.23/0.56          | ~ (v1_funct_1 @ X20)
% 0.23/0.56          | ~ (l1_pre_topc @ X19)
% 0.23/0.56          | ~ (v3_tdlat_3 @ X19)
% 0.23/0.56          | ~ (v2_pre_topc @ X19)
% 0.23/0.56          | (v2_struct_0 @ X19))),
% 0.23/0.56      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.23/0.56  thf('21', plain,
% 0.23/0.56      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.23/0.56         ((v2_struct_0 @ X19)
% 0.23/0.56          | ~ (v2_pre_topc @ X19)
% 0.23/0.56          | ~ (v3_tdlat_3 @ X19)
% 0.23/0.56          | ~ (l1_pre_topc @ X19)
% 0.23/0.56          | ~ (v1_funct_1 @ X20)
% 0.23/0.56          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.23/0.56          | ~ (v5_pre_topc @ X20 @ X19 @ X18)
% 0.23/0.56          | ~ (m1_subset_1 @ X20 @ 
% 0.23/0.56               (k1_zfmisc_1 @ 
% 0.23/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))))
% 0.23/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.23/0.56          | ((k8_relset_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18) @ X20 @ 
% 0.23/0.56              X22) = (k2_pre_topc @ X19 @ X22))
% 0.23/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.23/0.56          | ~ (v3_borsuk_1 @ X20 @ X19 @ X18)
% 0.23/0.56          | ~ (m1_pre_topc @ X18 @ X19)
% 0.23/0.56          | ~ (v4_tex_2 @ X18 @ X19)
% 0.23/0.56          | (v2_struct_0 @ X18))),
% 0.23/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.23/0.56  thf('22', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((v2_struct_0 @ sk_B_1)
% 0.23/0.56          | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.23/0.56          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.23/0.56          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B_1)
% 0.23/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.23/0.56          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.23/0.56              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.23/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.56          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.23/0.56          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.56               (u1_struct_0 @ sk_B_1))
% 0.23/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.23/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.56          | ~ (v3_tdlat_3 @ sk_A)
% 0.23/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.56          | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('sup-', [status(thm)], ['19', '21'])).
% 0.23/0.56  thf('23', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('24', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('25', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B_1)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('26', plain,
% 0.23/0.56      ((m1_subset_1 @ sk_C @ 
% 0.23/0.56        (k1_zfmisc_1 @ 
% 0.23/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(redefinition_k8_relset_1, axiom,
% 0.23/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.56       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.23/0.56  thf('27', plain,
% 0.23/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.23/0.56          | ((k8_relset_1 @ X4 @ X5 @ X3 @ X6) = (k10_relat_1 @ X3 @ X6)))),
% 0.23/0.56      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.23/0.56  thf('28', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.23/0.56           sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.56  thf('29', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('30', plain,
% 0.23/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('33', plain, ((v3_tdlat_3 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('35', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((v2_struct_0 @ sk_B_1)
% 0.23/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.23/0.56          | ((k10_relat_1 @ sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.23/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.56          | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('demod', [status(thm)],
% 0.23/0.56                ['22', '23', '24', '25', '28', '29', '30', '31', '32', '33', 
% 0.23/0.56                 '34'])).
% 0.23/0.56  thf('36', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.23/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.56        | ((k10_relat_1 @ sk_C @ (k1_tarski @ sk_D))
% 0.23/0.56            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.23/0.56        | (v2_struct_0 @ sk_B_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['18', '35'])).
% 0.23/0.56  thf('37', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (v2_struct_0 @ sk_B_1)
% 0.23/0.56        | ((k10_relat_1 @ sk_C @ (k1_tarski @ sk_D))
% 0.23/0.56            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['10', '36'])).
% 0.23/0.56  thf('38', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(t1_tsep_1, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( l1_pre_topc @ A ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.56           ( m1_subset_1 @
% 0.23/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.23/0.56  thf('39', plain,
% 0.23/0.56      (![X16 : $i, X17 : $i]:
% 0.23/0.56         (~ (m1_pre_topc @ X16 @ X17)
% 0.23/0.56          | (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.23/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.23/0.56          | ~ (l1_pre_topc @ X17))),
% 0.23/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.23/0.56  thf('40', plain,
% 0.23/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.23/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.23/0.56  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('42', plain,
% 0.23/0.56      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.23/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.23/0.56  thf(cc1_subset_1, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( v1_xboole_0 @ A ) =>
% 0.23/0.56       ( ![B:$i]:
% 0.23/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.23/0.56  thf('43', plain,
% 0.23/0.56      (![X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.23/0.56          | (v1_xboole_0 @ X1)
% 0.23/0.56          | ~ (v1_xboole_0 @ X2))),
% 0.23/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.23/0.56  thf('44', plain,
% 0.23/0.56      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.23/0.56  thf('45', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | ((k10_relat_1 @ sk_C @ (k1_tarski @ sk_D))
% 0.23/0.56            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.23/0.56        | (v2_struct_0 @ sk_B_1)
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['37', '44'])).
% 0.23/0.56  thf('46', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_B_1)
% 0.23/0.56        | ((k10_relat_1 @ sk_C @ (k1_tarski @ sk_D))
% 0.23/0.56            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.23/0.56  thf('47', plain,
% 0.23/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.56  thf('48', plain,
% 0.23/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.56  thf('49', plain,
% 0.23/0.56      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.23/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.23/0.56         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('50', plain, (((sk_D) = (sk_E))),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('51', plain,
% 0.23/0.56      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.23/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.23/0.56         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.23/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.23/0.56  thf('52', plain,
% 0.23/0.56      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.23/0.56          (k1_tarski @ sk_D))
% 0.23/0.56          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['48', '51'])).
% 0.23/0.56  thf('53', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.23/0.56           sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.23/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.56  thf('54', plain,
% 0.23/0.56      ((((k10_relat_1 @ sk_C @ (k1_tarski @ sk_D))
% 0.23/0.56          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.23/0.56  thf('55', plain,
% 0.23/0.56      ((((k10_relat_1 @ sk_C @ (k1_tarski @ sk_D))
% 0.23/0.56          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['47', '54'])).
% 0.23/0.56  thf('56', plain,
% 0.23/0.56      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.23/0.56  thf('57', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.23/0.56        | ((k10_relat_1 @ sk_C @ (k1_tarski @ sk_D))
% 0.23/0.56            != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))))),
% 0.23/0.56      inference('clc', [status(thm)], ['55', '56'])).
% 0.23/0.56  thf('58', plain,
% 0.23/0.56      ((((k10_relat_1 @ sk_C @ (k1_tarski @ sk_D))
% 0.23/0.56          != (k10_relat_1 @ sk_C @ (k1_tarski @ sk_D)))
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | (v2_struct_0 @ sk_B_1)
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['46', '57'])).
% 0.23/0.56  thf('59', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_B_1)
% 0.23/0.56        | (v2_struct_0 @ sk_A)
% 0.23/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.23/0.56      inference('simplify', [status(thm)], ['58'])).
% 0.23/0.56  thf('60', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('61', plain,
% 0.23/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.23/0.56      inference('clc', [status(thm)], ['59', '60'])).
% 0.23/0.56  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('63', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.23/0.56      inference('clc', [status(thm)], ['61', '62'])).
% 0.23/0.56  thf(rc7_pre_topc, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ?[B:$i]:
% 0.23/0.56         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.23/0.56           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.23/0.56  thf('64', plain,
% 0.23/0.56      (![X11 : $i]:
% 0.23/0.56         ((m1_subset_1 @ (sk_B @ X11) @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.23/0.56          | ~ (l1_pre_topc @ X11)
% 0.23/0.56          | ~ (v2_pre_topc @ X11)
% 0.23/0.56          | (v2_struct_0 @ X11))),
% 0.23/0.56      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.23/0.56  thf('65', plain,
% 0.23/0.56      (![X1 : $i, X2 : $i]:
% 0.23/0.56         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.23/0.56          | (v1_xboole_0 @ X1)
% 0.23/0.56          | ~ (v1_xboole_0 @ X2))),
% 0.23/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.23/0.56  thf('66', plain,
% 0.23/0.56      (![X0 : $i]:
% 0.23/0.56         ((v2_struct_0 @ X0)
% 0.23/0.56          | ~ (v2_pre_topc @ X0)
% 0.23/0.56          | ~ (l1_pre_topc @ X0)
% 0.23/0.56          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.23/0.56          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.23/0.56      inference('sup-', [status(thm)], ['64', '65'])).
% 0.23/0.56  thf('67', plain,
% 0.23/0.56      (((v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.23/0.56        | ~ (l1_pre_topc @ sk_B_1)
% 0.23/0.56        | ~ (v2_pre_topc @ sk_B_1)
% 0.23/0.56        | (v2_struct_0 @ sk_B_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['63', '66'])).
% 0.23/0.56  thf('68', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(dt_m1_pre_topc, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( l1_pre_topc @ A ) =>
% 0.23/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.23/0.56  thf('69', plain,
% 0.23/0.56      (![X9 : $i, X10 : $i]:
% 0.23/0.56         (~ (m1_pre_topc @ X9 @ X10)
% 0.23/0.56          | (l1_pre_topc @ X9)
% 0.23/0.56          | ~ (l1_pre_topc @ X10))),
% 0.23/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.23/0.56  thf('70', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.23/0.56  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('72', plain, ((l1_pre_topc @ sk_B_1)),
% 0.23/0.56      inference('demod', [status(thm)], ['70', '71'])).
% 0.23/0.56  thf('73', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf(cc1_pre_topc, axiom,
% 0.23/0.56    (![A:$i]:
% 0.23/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.23/0.56  thf('74', plain,
% 0.23/0.56      (![X7 : $i, X8 : $i]:
% 0.23/0.56         (~ (m1_pre_topc @ X7 @ X8)
% 0.23/0.56          | (v2_pre_topc @ X7)
% 0.23/0.56          | ~ (l1_pre_topc @ X8)
% 0.23/0.56          | ~ (v2_pre_topc @ X8))),
% 0.23/0.56      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.23/0.56  thf('75', plain,
% 0.23/0.56      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.56        | (v2_pre_topc @ sk_B_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.23/0.56  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('78', plain, ((v2_pre_topc @ sk_B_1)),
% 0.23/0.56      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.23/0.56  thf('79', plain,
% 0.23/0.56      (((v1_xboole_0 @ (sk_B @ sk_B_1)) | (v2_struct_0 @ sk_B_1))),
% 0.23/0.56      inference('demod', [status(thm)], ['67', '72', '78'])).
% 0.23/0.56  thf('80', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.23/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.56  thf('81', plain, ((v1_xboole_0 @ (sk_B @ sk_B_1))),
% 0.23/0.56      inference('clc', [status(thm)], ['79', '80'])).
% 0.23/0.56  thf('82', plain,
% 0.23/0.56      (![X11 : $i]:
% 0.23/0.56         (~ (v1_xboole_0 @ (sk_B @ X11))
% 0.23/0.56          | ~ (l1_pre_topc @ X11)
% 0.23/0.56          | ~ (v2_pre_topc @ X11)
% 0.23/0.56          | (v2_struct_0 @ X11))),
% 0.23/0.56      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.23/0.56  thf('83', plain,
% 0.23/0.56      (((v2_struct_0 @ sk_B_1)
% 0.23/0.56        | ~ (v2_pre_topc @ sk_B_1)
% 0.23/0.56        | ~ (l1_pre_topc @ sk_B_1))),
% 0.23/0.56      inference('sup-', [status(thm)], ['81', '82'])).
% 0.23/0.56  thf('84', plain, ((v2_pre_topc @ sk_B_1)),
% 0.23/0.56      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.23/0.56  thf('85', plain, ((l1_pre_topc @ sk_B_1)),
% 0.23/0.56      inference('demod', [status(thm)], ['70', '71'])).
% 0.23/0.56  thf('86', plain, ((v2_struct_0 @ sk_B_1)),
% 0.23/0.56      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.23/0.56  thf('87', plain, ($false), inference('demod', [status(thm)], ['0', '86'])).
% 0.23/0.56  
% 0.23/0.56  % SZS output end Refutation
% 0.23/0.56  
% 0.23/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
