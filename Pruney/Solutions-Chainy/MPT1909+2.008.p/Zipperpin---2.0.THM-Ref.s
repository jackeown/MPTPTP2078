%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Q2POjShRx

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 254 expanded)
%              Number of leaves         :   38 (  92 expanded)
%              Depth                    :   26
%              Number of atoms          : 1193 (7060 expanded)
%              Number of equality atoms :   28 ( 198 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('7',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('11',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_tex_2 @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( v3_borsuk_1 @ X21 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X22 != X23 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 @ X22 )
        = ( k2_pre_topc @ X20 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v5_pre_topc @ X21 @ X20 @ X19 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( v3_tdlat_3 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v5_pre_topc @ X21 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X19 ) @ X21 @ X23 )
        = ( k2_pre_topc @ X20 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_borsuk_1 @ X21 @ X20 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( v4_tex_2 @ X19 @ X20 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v4_tex_2 @ sk_B_2 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C @ sk_A @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v4_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
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
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30','31','32','33','34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['22','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('41',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('56',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('62',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['53','54','59','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( sk_B_1 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('69',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['48','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','71'])).

thf('73',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('74',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_B_2 ) )
      | ~ ( l1_pre_topc @ sk_B_2 )
      | ~ ( v2_pre_topc @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['57','58'])).

thf('78',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['1','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('90',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['57','58'])).

thf('91',plain,(
    v2_struct_0 @ sk_B_2 ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Q2POjShRx
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:04:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 181 iterations in 0.090s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.53  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.19/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.53  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.53  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.19/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.53  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.19/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.53  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.19/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.53  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.19/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.53  thf(t77_tex_2, conjecture,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.53         ( l1_pre_topc @ A ) ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.19/0.53             ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.53           ( ![C:$i]:
% 0.19/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.53                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.19/0.53                 ( m1_subset_1 @
% 0.19/0.53                   C @ 
% 0.19/0.53                   ( k1_zfmisc_1 @
% 0.19/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.53               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.19/0.53                 ( ![D:$i]:
% 0.19/0.53                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.53                     ( ![E:$i]:
% 0.19/0.53                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53                         ( ( ( D ) = ( E ) ) =>
% 0.19/0.53                           ( ( k8_relset_1 @
% 0.19/0.53                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.53                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.19/0.53                             ( k2_pre_topc @
% 0.19/0.53                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i]:
% 0.19/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.53            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.53          ( ![B:$i]:
% 0.19/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.19/0.53                ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.53              ( ![C:$i]:
% 0.19/0.53                ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.53                    ( v1_funct_2 @
% 0.19/0.53                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.53                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.19/0.53                    ( m1_subset_1 @
% 0.19/0.53                      C @ 
% 0.19/0.53                      ( k1_zfmisc_1 @
% 0.19/0.53                        ( k2_zfmisc_1 @
% 0.19/0.53                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.53                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.19/0.53                    ( ![D:$i]:
% 0.19/0.53                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.53                        ( ![E:$i]:
% 0.19/0.53                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.53                            ( ( ( D ) = ( E ) ) =>
% 0.19/0.53                              ( ( k8_relset_1 @
% 0.19/0.53                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.53                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.19/0.53                                ( k2_pre_topc @
% 0.19/0.53                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.19/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(d1_xboole_0, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.53  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('4', plain, (((sk_D) = (sk_E))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('5', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.19/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X17 : $i, X18 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X17)
% 0.19/0.53          | ~ (m1_subset_1 @ X18 @ X17)
% 0.19/0.53          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('8', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('9', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_2))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X17 : $i, X18 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X17)
% 0.19/0.53          | ~ (m1_subset_1 @ X18 @ X17)
% 0.19/0.53          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.19/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D) = (k1_tarski @ sk_D))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.53  thf('12', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_2))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf(dt_k6_domain_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.53       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X15 : $i, X16 : $i]:
% 0.19/0.53         ((v1_xboole_0 @ X15)
% 0.19/0.53          | ~ (m1_subset_1 @ X16 @ X15)
% 0.19/0.53          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.19/0.53      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D) @ 
% 0.19/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 0.19/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.54      inference('sup+', [status(thm)], ['11', '14'])).
% 0.19/0.54  thf('16', plain,
% 0.19/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 0.19/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.54  thf(t39_pre_topc, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.54               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X12 @ X13)
% 0.19/0.54          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.54          | ~ (l1_pre_topc @ X13))),
% 0.19/0.54      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.19/0.54  thf('18', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54          | ~ (l1_pre_topc @ X0)
% 0.19/0.54          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.19/0.54          | ~ (m1_pre_topc @ sk_B_2 @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['8', '18'])).
% 0.19/0.54  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('21', plain,
% 0.19/0.54      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.54  thf('22', plain,
% 0.19/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 0.19/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ 
% 0.19/0.54        (k1_zfmisc_1 @ 
% 0.19/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(t76_tex_2, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.19/0.54         ( l1_pre_topc @ A ) ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.19/0.54             ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.54                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.19/0.54                 ( m1_subset_1 @
% 0.19/0.54                   C @ 
% 0.19/0.54                   ( k1_zfmisc_1 @
% 0.19/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.54               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.19/0.54                 ( ![D:$i]:
% 0.19/0.54                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.54                     ( ![E:$i]:
% 0.19/0.54                       ( ( m1_subset_1 @
% 0.19/0.54                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54                         ( ( ( D ) = ( E ) ) =>
% 0.19/0.54                           ( ( k8_relset_1 @
% 0.19/0.54                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.54                               D ) =
% 0.19/0.54                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.54         ((v2_struct_0 @ X19)
% 0.19/0.54          | ~ (v4_tex_2 @ X19 @ X20)
% 0.19/0.54          | ~ (m1_pre_topc @ X19 @ X20)
% 0.19/0.54          | ~ (v3_borsuk_1 @ X21 @ X20 @ X19)
% 0.19/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54          | ((X22) != (X23))
% 0.19/0.54          | ((k8_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21 @ 
% 0.19/0.54              X22) = (k2_pre_topc @ X20 @ X23))
% 0.19/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.54          | ~ (m1_subset_1 @ X21 @ 
% 0.19/0.54               (k1_zfmisc_1 @ 
% 0.19/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.19/0.54          | ~ (v5_pre_topc @ X21 @ X20 @ X19)
% 0.19/0.54          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.19/0.54          | ~ (v1_funct_1 @ X21)
% 0.19/0.54          | ~ (l1_pre_topc @ X20)
% 0.19/0.54          | ~ (v3_tdlat_3 @ X20)
% 0.19/0.54          | ~ (v2_pre_topc @ X20)
% 0.19/0.54          | (v2_struct_0 @ X20))),
% 0.19/0.54      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i]:
% 0.19/0.54         ((v2_struct_0 @ X20)
% 0.19/0.54          | ~ (v2_pre_topc @ X20)
% 0.19/0.54          | ~ (v3_tdlat_3 @ X20)
% 0.19/0.54          | ~ (l1_pre_topc @ X20)
% 0.19/0.54          | ~ (v1_funct_1 @ X21)
% 0.19/0.54          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))
% 0.19/0.54          | ~ (v5_pre_topc @ X21 @ X20 @ X19)
% 0.19/0.54          | ~ (m1_subset_1 @ X21 @ 
% 0.19/0.54               (k1_zfmisc_1 @ 
% 0.19/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19))))
% 0.19/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.54          | ((k8_relset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X19) @ X21 @ 
% 0.19/0.54              X23) = (k2_pre_topc @ X20 @ X23))
% 0.19/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54          | ~ (v3_borsuk_1 @ X21 @ X20 @ X19)
% 0.19/0.54          | ~ (m1_pre_topc @ X19 @ X20)
% 0.19/0.54          | ~ (v4_tex_2 @ X19 @ X20)
% 0.19/0.54          | (v2_struct_0 @ X19))),
% 0.19/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.54  thf('26', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_B_2)
% 0.19/0.54          | ~ (v4_tex_2 @ sk_B_2 @ sk_A)
% 0.19/0.54          | ~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 0.19/0.54          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B_2)
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 0.19/0.54          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 0.19/0.54              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_2)
% 0.19/0.54          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.54               (u1_struct_0 @ sk_B_2))
% 0.19/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.19/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.54          | ~ (v3_tdlat_3 @ sk_A)
% 0.19/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.54          | (v2_struct_0 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['23', '25'])).
% 0.19/0.54  thf('27', plain, ((v4_tex_2 @ sk_B_2 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('28', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('29', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B_2)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('30', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B_2)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('34', plain, ((v3_tdlat_3 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('36', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_B_2)
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 0.19/0.54          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 0.19/0.54              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54          | (v2_struct_0 @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)],
% 0.19/0.54                ['26', '27', '28', '29', '30', '31', '32', '33', '34', '35'])).
% 0.19/0.54  thf('37', plain,
% 0.19/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54        | (v2_struct_0 @ sk_A)
% 0.19/0.54        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.19/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 0.19/0.54            sk_C @ (k1_tarski @ sk_D))
% 0.19/0.54            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.19/0.54        | (v2_struct_0 @ sk_B_2))),
% 0.19/0.54      inference('sup-', [status(thm)], ['22', '36'])).
% 0.19/0.54  thf('38', plain,
% 0.19/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54        | (v2_struct_0 @ sk_B_2)
% 0.19/0.54        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 0.19/0.54            sk_C @ (k1_tarski @ sk_D))
% 0.19/0.54            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.19/0.54        | (v2_struct_0 @ sk_A)
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['21', '37'])).
% 0.19/0.54  thf('39', plain,
% 0.19/0.54      (((v2_struct_0 @ sk_A)
% 0.19/0.54        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 0.19/0.54            sk_C @ (k1_tarski @ sk_D))
% 0.19/0.54            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.19/0.54        | (v2_struct_0 @ sk_B_2)
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.54  thf('40', plain,
% 0.19/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D) = (k1_tarski @ sk_D))
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.54  thf('41', plain,
% 0.19/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C @ 
% 0.19/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D))
% 0.19/0.54         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('42', plain, (((sk_D) = (sk_E))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('43', plain,
% 0.19/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C @ 
% 0.19/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D))
% 0.19/0.54         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.19/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.54  thf('44', plain,
% 0.19/0.54      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ sk_C @ 
% 0.19/0.54          (k1_tarski @ sk_D))
% 0.19/0.54          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['40', '43'])).
% 0.19/0.54  thf('45', plain,
% 0.19/0.54      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.19/0.54          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54        | (v2_struct_0 @ sk_B_2)
% 0.19/0.54        | (v2_struct_0 @ sk_A)
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['39', '44'])).
% 0.19/0.54  thf('46', plain,
% 0.19/0.54      (((v2_struct_0 @ sk_A)
% 0.19/0.54        | (v2_struct_0 @ sk_B_2)
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.19/0.54            != (k2_pre_topc @ sk_A @ 
% 0.19/0.54                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.19/0.54      inference('simplify', [status(thm)], ['45'])).
% 0.19/0.54  thf('47', plain,
% 0.19/0.54      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.19/0.54          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54        | (v2_struct_0 @ sk_B_2)
% 0.19/0.54        | (v2_struct_0 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['7', '46'])).
% 0.19/0.54  thf('48', plain,
% 0.19/0.54      (((v2_struct_0 @ sk_A)
% 0.19/0.54        | (v2_struct_0 @ sk_B_2)
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.19/0.54  thf('49', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(rc7_pre_topc, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.54       ( ?[B:$i]:
% 0.19/0.54         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.54           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.54  thf('50', plain,
% 0.19/0.54      (![X11 : $i]:
% 0.19/0.54         ((m1_subset_1 @ (sk_B_1 @ X11) @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.19/0.54          | ~ (l1_pre_topc @ X11)
% 0.19/0.54          | ~ (v2_pre_topc @ X11)
% 0.19/0.54          | (v2_struct_0 @ X11))),
% 0.19/0.54      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.19/0.54  thf('51', plain,
% 0.19/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X12 @ X13)
% 0.19/0.54          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.54          | ~ (l1_pre_topc @ X13))),
% 0.19/0.54      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.19/0.54  thf('52', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((v2_struct_0 @ X0)
% 0.19/0.54          | ~ (v2_pre_topc @ X0)
% 0.19/0.54          | ~ (l1_pre_topc @ X0)
% 0.19/0.54          | ~ (l1_pre_topc @ X1)
% 0.19/0.54          | (m1_subset_1 @ (sk_B_1 @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.19/0.54          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.19/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.54  thf('53', plain,
% 0.19/0.54      (((m1_subset_1 @ (sk_B_1 @ sk_B_2) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.54        | ~ (l1_pre_topc @ sk_B_2)
% 0.19/0.54        | ~ (v2_pre_topc @ sk_B_2)
% 0.19/0.54        | (v2_struct_0 @ sk_B_2))),
% 0.19/0.54      inference('sup-', [status(thm)], ['49', '52'])).
% 0.19/0.54  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('55', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(dt_m1_pre_topc, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.54  thf('56', plain,
% 0.19/0.54      (![X9 : $i, X10 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X9 @ X10)
% 0.19/0.54          | (l1_pre_topc @ X9)
% 0.19/0.54          | ~ (l1_pre_topc @ X10))),
% 0.19/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.54  thf('57', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_2))),
% 0.19/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.54  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('59', plain, ((l1_pre_topc @ sk_B_2)),
% 0.19/0.54      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.54  thf('60', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(cc1_pre_topc, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.19/0.54  thf('61', plain,
% 0.19/0.54      (![X7 : $i, X8 : $i]:
% 0.19/0.54         (~ (m1_pre_topc @ X7 @ X8)
% 0.19/0.54          | (v2_pre_topc @ X7)
% 0.19/0.54          | ~ (l1_pre_topc @ X8)
% 0.19/0.54          | ~ (v2_pre_topc @ X8))),
% 0.19/0.54      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.19/0.54  thf('62', plain,
% 0.19/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.54        | (v2_pre_topc @ sk_B_2))),
% 0.19/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.54  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('65', plain, ((v2_pre_topc @ sk_B_2)),
% 0.19/0.54      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.19/0.54  thf('66', plain,
% 0.19/0.54      (((m1_subset_1 @ (sk_B_1 @ sk_B_2) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54        | (v2_struct_0 @ sk_B_2))),
% 0.19/0.54      inference('demod', [status(thm)], ['53', '54', '59', '65'])).
% 0.19/0.54  thf('67', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('68', plain,
% 0.19/0.54      ((m1_subset_1 @ (sk_B_1 @ sk_B_2) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('clc', [status(thm)], ['66', '67'])).
% 0.19/0.54  thf(t5_subset, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.19/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.19/0.54  thf('69', plain,
% 0.19/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X4 @ X5)
% 0.19/0.54          | ~ (v1_xboole_0 @ X6)
% 0.19/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.54  thf('70', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.54          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_B_2)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.19/0.54  thf('71', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 0.19/0.54          | (v2_struct_0 @ sk_B_2)
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_B_2)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['48', '70'])).
% 0.19/0.54  thf('72', plain,
% 0.19/0.54      (((v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.19/0.54        | (v2_struct_0 @ sk_A)
% 0.19/0.54        | (v2_struct_0 @ sk_B_2)
% 0.19/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['2', '71'])).
% 0.19/0.54  thf('73', plain,
% 0.19/0.54      (![X11 : $i]:
% 0.19/0.54         ((m1_subset_1 @ (sk_B_1 @ X11) @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.19/0.54          | ~ (l1_pre_topc @ X11)
% 0.19/0.54          | ~ (v2_pre_topc @ X11)
% 0.19/0.54          | (v2_struct_0 @ X11))),
% 0.19/0.54      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.19/0.54  thf('74', plain,
% 0.19/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X4 @ X5)
% 0.19/0.54          | ~ (v1_xboole_0 @ X6)
% 0.19/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.54  thf('75', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((v2_struct_0 @ X0)
% 0.19/0.54          | ~ (v2_pre_topc @ X0)
% 0.19/0.54          | ~ (l1_pre_topc @ X0)
% 0.19/0.54          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.19/0.54          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.19/0.54  thf('76', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_B_2)
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.19/0.54          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_B_2))
% 0.19/0.54          | ~ (l1_pre_topc @ sk_B_2)
% 0.19/0.54          | ~ (v2_pre_topc @ sk_B_2)
% 0.19/0.54          | (v2_struct_0 @ sk_B_2))),
% 0.19/0.54      inference('sup-', [status(thm)], ['72', '75'])).
% 0.19/0.54  thf('77', plain, ((l1_pre_topc @ sk_B_2)),
% 0.19/0.54      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.54  thf('78', plain, ((v2_pre_topc @ sk_B_2)),
% 0.19/0.54      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.19/0.54  thf('79', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_B_2)
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.19/0.54          | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_B_2))
% 0.19/0.54          | (v2_struct_0 @ sk_B_2))),
% 0.19/0.54      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.19/0.54  thf('80', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_B_2))
% 0.19/0.54          | (v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.19/0.54          | (v2_struct_0 @ sk_A)
% 0.19/0.54          | (v2_struct_0 @ sk_B_2))),
% 0.19/0.54      inference('simplify', [status(thm)], ['79'])).
% 0.19/0.54  thf('81', plain,
% 0.19/0.54      (((v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 0.19/0.54        | (v2_struct_0 @ sk_B_2)
% 0.19/0.54        | (v2_struct_0 @ sk_A)
% 0.19/0.54        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['1', '80'])).
% 0.19/0.54  thf('82', plain,
% 0.19/0.54      (((v2_struct_0 @ sk_A)
% 0.19/0.54        | (v2_struct_0 @ sk_B_2)
% 0.19/0.54        | (v1_xboole_0 @ (sk_B_1 @ sk_B_2)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['81'])).
% 0.19/0.54  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('84', plain,
% 0.19/0.54      (((v1_xboole_0 @ (sk_B_1 @ sk_B_2)) | (v2_struct_0 @ sk_B_2))),
% 0.19/0.54      inference('clc', [status(thm)], ['82', '83'])).
% 0.19/0.54  thf('85', plain, (~ (v2_struct_0 @ sk_B_2)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('86', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_B_2))),
% 0.19/0.54      inference('clc', [status(thm)], ['84', '85'])).
% 0.19/0.54  thf('87', plain,
% 0.19/0.54      (![X11 : $i]:
% 0.19/0.54         (~ (v1_xboole_0 @ (sk_B_1 @ X11))
% 0.19/0.54          | ~ (l1_pre_topc @ X11)
% 0.19/0.54          | ~ (v2_pre_topc @ X11)
% 0.19/0.54          | (v2_struct_0 @ X11))),
% 0.19/0.54      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.19/0.54  thf('88', plain,
% 0.19/0.54      (((v2_struct_0 @ sk_B_2)
% 0.19/0.54        | ~ (v2_pre_topc @ sk_B_2)
% 0.19/0.54        | ~ (l1_pre_topc @ sk_B_2))),
% 0.19/0.54      inference('sup-', [status(thm)], ['86', '87'])).
% 0.19/0.54  thf('89', plain, ((v2_pre_topc @ sk_B_2)),
% 0.19/0.54      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.19/0.54  thf('90', plain, ((l1_pre_topc @ sk_B_2)),
% 0.19/0.54      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.54  thf('91', plain, ((v2_struct_0 @ sk_B_2)),
% 0.19/0.54      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.19/0.54  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
