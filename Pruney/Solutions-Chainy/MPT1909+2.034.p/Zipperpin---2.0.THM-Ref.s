%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lpz0PRgQ27

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 211 expanded)
%              Number of leaves         :   35 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          : 1126 (6180 expanded)
%              Number of equality atoms :   30 ( 181 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( ( k6_domain_1 @ X8 @ X9 )
        = ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( ( k6_domain_1 @ X8 @ X9 )
        = ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('17',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v4_tex_2 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v3_borsuk_1 @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( X20 != X21 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 @ X20 )
        = ( k2_pre_topc @ X18 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v5_pre_topc @ X19 @ X18 @ X17 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v3_tdlat_3 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( v3_tdlat_3 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v5_pre_topc @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X17 ) @ X19 @ X21 )
        = ( k2_pre_topc @ X18 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_borsuk_1 @ X19 @ X18 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v4_tex_2 @ X17 @ X18 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_tex_2 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30','31','32','33','34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','37'])).

thf('39',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('40',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( v4_tex_2 @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ( v3_tex_2 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_tex_2 @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( v4_tex_2 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v4_tex_2 @ sk_B @ sk_A )
    | ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_tex_2 @ ( u1_struct_0 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','77'])).

thf('79',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['59','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lpz0PRgQ27
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:52:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 117 iterations in 0.083s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(t77_tex_2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                     ( ![E:$i]:
% 0.20/0.51                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.51                           ( ( k8_relset_1 @
% 0.20/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.51                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.51                             ( k2_pre_topc @
% 0.20/0.51                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.51                ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                    ( v1_funct_2 @
% 0.20/0.51                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.51                    ( m1_subset_1 @
% 0.20/0.51                      C @ 
% 0.20/0.51                      ( k1_zfmisc_1 @
% 0.20/0.51                        ( k2_zfmisc_1 @
% 0.20/0.51                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.51                    ( ![D:$i]:
% 0.20/0.51                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                        ( ![E:$i]:
% 0.20/0.51                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                            ( ( ( D ) = ( E ) ) =>
% 0.20/0.51                              ( ( k8_relset_1 @
% 0.20/0.51                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.51                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.51                                ( k2_pre_topc @
% 0.20/0.51                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.20/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t2_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X2)
% 0.20/0.51          | (v1_xboole_0 @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('5', plain, (((sk_D) = (sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X8)
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ X8)
% 0.20/0.51          | ((k6_domain_1 @ X8 @ X9) = (k1_tarski @ X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('10', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(dt_k6_domain_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X6)
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ X6)
% 0.20/0.51          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['9', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.51  thf('15', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X8)
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ X8)
% 0.20/0.51          | ((k6_domain_1 @ X8 @ X9) = (k1_tarski @ X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ X6)
% 0.20/0.51          | ~ (m1_subset_1 @ X7 @ X6)
% 0.20/0.51          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t76_tex_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.51         ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.51             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.51                     ( ![E:$i]:
% 0.20/0.51                       ( ( m1_subset_1 @
% 0.20/0.51                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.51                           ( ( k8_relset_1 @
% 0.20/0.51                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.51                               D ) =
% 0.20/0.51                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X17)
% 0.20/0.51          | ~ (v4_tex_2 @ X17 @ X18)
% 0.20/0.51          | ~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.51          | ~ (v3_borsuk_1 @ X19 @ X18 @ X17)
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.51          | ((X20) != (X21))
% 0.20/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19 @ 
% 0.20/0.51              X20) = (k2_pre_topc @ X18 @ X21))
% 0.20/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))))
% 0.20/0.51          | ~ (v5_pre_topc @ X19 @ X18 @ X17)
% 0.20/0.51          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.20/0.51          | ~ (v1_funct_1 @ X19)
% 0.20/0.51          | ~ (l1_pre_topc @ X18)
% 0.20/0.51          | ~ (v3_tdlat_3 @ X18)
% 0.20/0.51          | ~ (v2_pre_topc @ X18)
% 0.20/0.51          | (v2_struct_0 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X18)
% 0.20/0.51          | ~ (v2_pre_topc @ X18)
% 0.20/0.51          | ~ (v3_tdlat_3 @ X18)
% 0.20/0.51          | ~ (l1_pre_topc @ X18)
% 0.20/0.51          | ~ (v1_funct_1 @ X19)
% 0.20/0.51          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))
% 0.20/0.51          | ~ (v5_pre_topc @ X19 @ X18 @ X17)
% 0.20/0.51          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17))))
% 0.20/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.51          | ((k8_relset_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X17) @ X19 @ 
% 0.20/0.51              X21) = (k2_pre_topc @ X18 @ X21))
% 0.20/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.51          | ~ (v3_borsuk_1 @ X19 @ X18 @ X17)
% 0.20/0.51          | ~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.51          | ~ (v4_tex_2 @ X17 @ X18)
% 0.20/0.51          | (v2_struct_0 @ X17))),
% 0.20/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.51          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51               (u1_struct_0 @ sk_B))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.51  thf('27', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('32', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['26', '27', '28', '29', '30', '31', '32', '33', '34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51            sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.51            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51            sk_C_1 @ (k1_tarski @ sk_D))
% 0.20/0.51            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain, (((sk_D) = (sk_E))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.20/0.51         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.20/0.51         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 0.20/0.51          (k1_tarski @ sk_D))
% 0.20/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.51          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.51            != (k2_pre_topc @ sk_A @ 
% 0.20/0.51                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.51          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.51  thf('48', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t1_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( m1_subset_1 @
% 0.20/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.51          | (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.51          | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf(t5_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.51          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.51          | ~ (v1_xboole_0 @ X5)
% 0.20/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51          | (v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '54'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.51  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf(t46_tex_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.51          | ~ (v3_tex_2 @ X15 @ X16)
% 0.20/0.51          | ~ (l1_pre_topc @ X16)
% 0.20/0.51          | ~ (v2_pre_topc @ X16)
% 0.20/0.51          | (v2_struct_0 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.51        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.51  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.51        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.20/0.51  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.51        | ~ (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf(d8_tex_2, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( ( v4_tex_2 @ B @ A ) <=>
% 0.20/0.51             ( ![C:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | ~ (v4_tex_2 @ X12 @ X13)
% 0.20/0.51          | ((X14) != (u1_struct_0 @ X12))
% 0.20/0.51          | (v3_tex_2 @ X14 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.51          | ~ (l1_pre_topc @ X13)
% 0.20/0.51          | (v2_struct_0 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X13)
% 0.20/0.51          | ~ (l1_pre_topc @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.51          | (v3_tex_2 @ (u1_struct_0 @ X12) @ X13)
% 0.20/0.51          | ~ (v4_tex_2 @ X12 @ X13)
% 0.20/0.51          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.20/0.51      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.51        | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.20/0.51        | (v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['68', '70'])).
% 0.20/0.51  thf('72', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.20/0.51  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('77', plain, ((v3_tex_2 @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['75', '76'])).
% 0.20/0.51  thf('78', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['67', '77'])).
% 0.20/0.51  thf('79', plain, ((v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('clc', [status(thm)], ['59', '78'])).
% 0.20/0.51  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
