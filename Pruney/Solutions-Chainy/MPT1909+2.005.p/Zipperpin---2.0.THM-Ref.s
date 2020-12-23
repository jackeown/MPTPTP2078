%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U30bi8FC79

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:47 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 284 expanded)
%              Number of leaves         :   44 ( 101 expanded)
%              Depth                    :   24
%              Number of atoms          : 1304 (8099 expanded)
%              Number of equality atoms :   28 ( 226 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    ! [X51: $i,X52: $i] :
      ( ( v1_xboole_0 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ X51 )
      | ( ( k6_domain_1 @ X51 @ X52 )
        = ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X51: $i,X52: $i] :
      ( ( v1_xboole_0 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ X51 )
      | ( ( k6_domain_1 @ X51 @ X52 )
        = ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X49: $i,X50: $i] :
      ( ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ X49 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X49 @ X50 ) @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_pre_topc @ X46 @ X47 )
      | ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ) ) ),
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

thf('22',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ( v2_struct_0 @ X60 )
      | ~ ( v4_tex_2 @ X60 @ X61 )
      | ~ ( m1_pre_topc @ X60 @ X61 )
      | ~ ( v3_borsuk_1 @ X62 @ X61 @ X60 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( X63 != X64 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X60 ) @ X62 @ X63 )
        = ( k2_pre_topc @ X61 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X60 ) ) ) )
      | ~ ( v5_pre_topc @ X62 @ X61 @ X60 )
      | ~ ( v1_funct_2 @ X62 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X60 ) )
      | ~ ( v1_funct_1 @ X62 )
      | ~ ( l1_pre_topc @ X61 )
      | ~ ( v3_tdlat_3 @ X61 )
      | ~ ( v2_pre_topc @ X61 )
      | ( v2_struct_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('23',plain,(
    ! [X60: $i,X61: $i,X62: $i,X64: $i] :
      ( ( v2_struct_0 @ X61 )
      | ~ ( v2_pre_topc @ X61 )
      | ~ ( v3_tdlat_3 @ X61 )
      | ~ ( l1_pre_topc @ X61 )
      | ~ ( v1_funct_1 @ X62 )
      | ~ ( v1_funct_2 @ X62 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X60 ) )
      | ~ ( v5_pre_topc @ X62 @ X61 @ X60 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X60 ) ) ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X61 ) @ ( u1_struct_0 @ X60 ) @ X62 @ X64 )
        = ( k2_pre_topc @ X61 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( v3_borsuk_1 @ X62 @ X61 @ X60 )
      | ~ ( m1_pre_topc @ X60 @ X61 )
      | ~ ( v4_tex_2 @ X60 @ X61 )
      | ( v2_struct_0 @ X60 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v4_tex_2 @ sk_B_2 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_2 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v4_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_2 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28','29','30','31','32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['19','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('39',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_2 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_2 ) @ sk_C_1 @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_pre_topc @ X53 @ X54 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X53 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('52',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( v1_xboole_0 @ X37 )
      | ~ ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('53',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(t66_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_tex_2 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X59: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X59 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X59 )
      | ~ ( v3_tdlat_3 @ X59 )
      | ~ ( v2_pre_topc @ X59 )
      | ( v2_struct_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t66_tex_2])).

thf('61',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( v1_xboole_0 @ X37 )
      | ~ ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ~ ( l1_pre_topc @ sk_B_2 )
    | ~ ( v3_tdlat_3 @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('65',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_pre_topc @ X44 @ X45 )
      | ( l1_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc9_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ~ ( v2_struct_0 @ B )
           => ( ~ ( v2_struct_0 @ B )
              & ( v3_tdlat_3 @ B ) ) ) ) ) )).

thf('70',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_pre_topc @ X55 @ X56 )
      | ( v3_tdlat_3 @ X55 )
      | ( v2_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X56 )
      | ~ ( v3_tdlat_3 @ X56 )
      | ~ ( v2_pre_topc @ X56 )
      | ( v2_struct_0 @ X56 ) ) ),
    inference(cnf,[status(esa)],[cc9_tdlat_3])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v3_tdlat_3 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_2 )
    | ( v3_tdlat_3 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v3_tdlat_3 @ sk_B_2 )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v3_tdlat_3 @ sk_B_2 ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('81',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('82',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['63','68','79','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X59: $i] :
      ( ( v3_tex_2 @ ( sk_B_1 @ X59 ) @ X59 )
      | ~ ( l1_pre_topc @ X59 )
      | ~ ( v3_tdlat_3 @ X59 )
      | ~ ( v2_pre_topc @ X59 )
      | ( v2_struct_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t66_tex_2])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('93',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( v1_xboole_0 @ X57 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ~ ( v3_tex_2 @ X57 @ X58 )
      | ~ ( l1_pre_topc @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ( v2_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B_2 )
    | ~ ( v2_pre_topc @ sk_B_2 )
    | ~ ( v3_tdlat_3 @ sk_B_2 )
    | ~ ( l1_pre_topc @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['88','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('102',plain,(
    v3_tdlat_3 @ sk_B_2 ),
    inference(clc,[status(thm)],['77','78'])).

thf('103',plain,(
    l1_pre_topc @ sk_B_2 ),
    inference(demod,[status(thm)],['66','67'])).

thf('104',plain,(
    v2_struct_0 @ sk_B_2 ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U30bi8FC79
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.74/1.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.98  % Solved by: fo/fo7.sh
% 1.74/1.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.98  % done 1206 iterations in 1.523s
% 1.74/1.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.98  % SZS output start Refutation
% 1.74/1.98  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 1.74/1.98  thf(sk_D_type, type, sk_D: $i).
% 1.74/1.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.98  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 1.74/1.98  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.74/1.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.74/1.98  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.74/1.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.74/1.98  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 1.74/1.98  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.74/1.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.74/1.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.74/1.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.74/1.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.74/1.98  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.98  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.74/1.98  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.74/1.98  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.74/1.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.74/1.98  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.74/1.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.74/1.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.74/1.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.74/1.98  thf(sk_E_type, type, sk_E: $i).
% 1.74/1.98  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 1.74/1.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.74/1.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.74/1.98  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.74/1.98  thf(t77_tex_2, conjecture,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 1.74/1.98         ( l1_pre_topc @ A ) ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 1.74/1.98             ( m1_pre_topc @ B @ A ) ) =>
% 1.74/1.98           ( ![C:$i]:
% 1.74/1.98             ( ( ( v1_funct_1 @ C ) & 
% 1.74/1.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.74/1.98                 ( v5_pre_topc @ C @ A @ B ) & 
% 1.74/1.98                 ( m1_subset_1 @
% 1.74/1.98                   C @ 
% 1.74/1.98                   ( k1_zfmisc_1 @
% 1.74/1.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.74/1.98               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 1.74/1.98                 ( ![D:$i]:
% 1.74/1.98                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 1.74/1.98                     ( ![E:$i]:
% 1.74/1.98                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 1.74/1.98                         ( ( ( D ) = ( E ) ) =>
% 1.74/1.98                           ( ( k8_relset_1 @
% 1.74/1.98                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.74/1.98                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 1.74/1.98                             ( k2_pre_topc @
% 1.74/1.98                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.98    (~( ![A:$i]:
% 1.74/1.98        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.74/1.98            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.98          ( ![B:$i]:
% 1.74/1.98            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 1.74/1.98                ( m1_pre_topc @ B @ A ) ) =>
% 1.74/1.98              ( ![C:$i]:
% 1.74/1.98                ( ( ( v1_funct_1 @ C ) & 
% 1.74/1.98                    ( v1_funct_2 @
% 1.74/1.98                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.74/1.98                    ( v5_pre_topc @ C @ A @ B ) & 
% 1.74/1.98                    ( m1_subset_1 @
% 1.74/1.98                      C @ 
% 1.74/1.98                      ( k1_zfmisc_1 @
% 1.74/1.98                        ( k2_zfmisc_1 @
% 1.74/1.98                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.74/1.98                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 1.74/1.98                    ( ![D:$i]:
% 1.74/1.98                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 1.74/1.98                        ( ![E:$i]:
% 1.74/1.98                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 1.74/1.98                            ( ( ( D ) = ( E ) ) =>
% 1.74/1.98                              ( ( k8_relset_1 @
% 1.74/1.98                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 1.74/1.98                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 1.74/1.98                                ( k2_pre_topc @
% 1.74/1.98                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.74/1.98    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 1.74/1.98  thf('0', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('1', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('2', plain, (((sk_D) = (sk_E))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 1.74/1.98      inference('demod', [status(thm)], ['1', '2'])).
% 1.74/1.98  thf(redefinition_k6_domain_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.74/1.98       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.74/1.98  thf('4', plain,
% 1.74/1.98      (![X51 : $i, X52 : $i]:
% 1.74/1.98         ((v1_xboole_0 @ X51)
% 1.74/1.98          | ~ (m1_subset_1 @ X52 @ X51)
% 1.74/1.98          | ((k6_domain_1 @ X51 @ X52) = (k1_tarski @ X52)))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.74/1.98  thf('5', plain,
% 1.74/1.98      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['3', '4'])).
% 1.74/1.98  thf('6', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('7', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_2))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('8', plain,
% 1.74/1.98      (![X51 : $i, X52 : $i]:
% 1.74/1.98         ((v1_xboole_0 @ X51)
% 1.74/1.98          | ~ (m1_subset_1 @ X52 @ X51)
% 1.74/1.98          | ((k6_domain_1 @ X51 @ X52) = (k1_tarski @ X52)))),
% 1.74/1.98      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.74/1.98  thf('9', plain,
% 1.74/1.98      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D) = (k1_tarski @ sk_D))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['7', '8'])).
% 1.74/1.98  thf('10', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_2))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(dt_k6_domain_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.74/1.98       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.74/1.98  thf('11', plain,
% 1.74/1.98      (![X49 : $i, X50 : $i]:
% 1.74/1.98         ((v1_xboole_0 @ X49)
% 1.74/1.98          | ~ (m1_subset_1 @ X50 @ X49)
% 1.74/1.98          | (m1_subset_1 @ (k6_domain_1 @ X49 @ X50) @ (k1_zfmisc_1 @ X49)))),
% 1.74/1.98      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 1.74/1.98  thf('12', plain,
% 1.74/1.98      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D) @ 
% 1.74/1.98         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['10', '11'])).
% 1.74/1.98  thf('13', plain,
% 1.74/1.98      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.74/1.98         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup+', [status(thm)], ['9', '12'])).
% 1.74/1.98  thf('14', plain,
% 1.74/1.98      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.74/1.98           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.98      inference('simplify', [status(thm)], ['13'])).
% 1.74/1.98  thf(t39_pre_topc, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( l1_pre_topc @ A ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( m1_pre_topc @ B @ A ) =>
% 1.74/1.98           ( ![C:$i]:
% 1.74/1.98             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.74/1.98               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 1.74/1.98  thf('15', plain,
% 1.74/1.98      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.74/1.98         (~ (m1_pre_topc @ X46 @ X47)
% 1.74/1.98          | (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.74/1.98          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 1.74/1.98          | ~ (l1_pre_topc @ X47))),
% 1.74/1.98      inference('cnf', [status(esa)], [t39_pre_topc])).
% 1.74/1.98  thf('16', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98          | ~ (l1_pre_topc @ X0)
% 1.74/1.98          | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.74/1.98             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.74/1.98          | ~ (m1_pre_topc @ sk_B_2 @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['14', '15'])).
% 1.74/1.98  thf('17', plain,
% 1.74/1.98      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.74/1.98         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.74/1.98        | ~ (l1_pre_topc @ sk_A)
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['6', '16'])).
% 1.74/1.98  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('19', plain,
% 1.74/1.98      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.74/1.98         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('demod', [status(thm)], ['17', '18'])).
% 1.74/1.98  thf('20', plain,
% 1.74/1.98      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.74/1.98           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.98      inference('simplify', [status(thm)], ['13'])).
% 1.74/1.98  thf('21', plain,
% 1.74/1.98      ((m1_subset_1 @ sk_C_1 @ 
% 1.74/1.98        (k1_zfmisc_1 @ 
% 1.74/1.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(t76_tex_2, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 1.74/1.98         ( l1_pre_topc @ A ) ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 1.74/1.98             ( m1_pre_topc @ B @ A ) ) =>
% 1.74/1.98           ( ![C:$i]:
% 1.74/1.98             ( ( ( v1_funct_1 @ C ) & 
% 1.74/1.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.74/1.98                 ( v5_pre_topc @ C @ A @ B ) & 
% 1.74/1.98                 ( m1_subset_1 @
% 1.74/1.98                   C @ 
% 1.74/1.98                   ( k1_zfmisc_1 @
% 1.74/1.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.74/1.98               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 1.74/1.98                 ( ![D:$i]:
% 1.74/1.98                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.74/1.98                     ( ![E:$i]:
% 1.74/1.98                       ( ( m1_subset_1 @
% 1.74/1.98                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.74/1.98                         ( ( ( D ) = ( E ) ) =>
% 1.74/1.98                           ( ( k8_relset_1 @
% 1.74/1.98                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.74/1.98                               D ) =
% 1.74/1.98                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.74/1.98  thf('22', plain,
% 1.74/1.98      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 1.74/1.98         ((v2_struct_0 @ X60)
% 1.74/1.98          | ~ (v4_tex_2 @ X60 @ X61)
% 1.74/1.98          | ~ (m1_pre_topc @ X60 @ X61)
% 1.74/1.98          | ~ (v3_borsuk_1 @ X62 @ X61 @ X60)
% 1.74/1.98          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 1.74/1.98          | ((X63) != (X64))
% 1.74/1.98          | ((k8_relset_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X60) @ X62 @ 
% 1.74/1.98              X63) = (k2_pre_topc @ X61 @ X64))
% 1.74/1.98          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 1.74/1.98          | ~ (m1_subset_1 @ X62 @ 
% 1.74/1.98               (k1_zfmisc_1 @ 
% 1.74/1.98                (k2_zfmisc_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X60))))
% 1.74/1.98          | ~ (v5_pre_topc @ X62 @ X61 @ X60)
% 1.74/1.98          | ~ (v1_funct_2 @ X62 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X60))
% 1.74/1.98          | ~ (v1_funct_1 @ X62)
% 1.74/1.98          | ~ (l1_pre_topc @ X61)
% 1.74/1.98          | ~ (v3_tdlat_3 @ X61)
% 1.74/1.98          | ~ (v2_pre_topc @ X61)
% 1.74/1.98          | (v2_struct_0 @ X61))),
% 1.74/1.98      inference('cnf', [status(esa)], [t76_tex_2])).
% 1.74/1.98  thf('23', plain,
% 1.74/1.98      (![X60 : $i, X61 : $i, X62 : $i, X64 : $i]:
% 1.74/1.98         ((v2_struct_0 @ X61)
% 1.74/1.98          | ~ (v2_pre_topc @ X61)
% 1.74/1.98          | ~ (v3_tdlat_3 @ X61)
% 1.74/1.98          | ~ (l1_pre_topc @ X61)
% 1.74/1.98          | ~ (v1_funct_1 @ X62)
% 1.74/1.98          | ~ (v1_funct_2 @ X62 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X60))
% 1.74/1.98          | ~ (v5_pre_topc @ X62 @ X61 @ X60)
% 1.74/1.98          | ~ (m1_subset_1 @ X62 @ 
% 1.74/1.98               (k1_zfmisc_1 @ 
% 1.74/1.98                (k2_zfmisc_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X60))))
% 1.74/1.98          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 1.74/1.98          | ((k8_relset_1 @ (u1_struct_0 @ X61) @ (u1_struct_0 @ X60) @ X62 @ 
% 1.74/1.98              X64) = (k2_pre_topc @ X61 @ X64))
% 1.74/1.98          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 1.74/1.98          | ~ (v3_borsuk_1 @ X62 @ X61 @ X60)
% 1.74/1.98          | ~ (m1_pre_topc @ X60 @ X61)
% 1.74/1.98          | ~ (v4_tex_2 @ X60 @ X61)
% 1.74/1.98          | (v2_struct_0 @ X60))),
% 1.74/1.98      inference('simplify', [status(thm)], ['22'])).
% 1.74/1.98  thf('24', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((v2_struct_0 @ sk_B_2)
% 1.74/1.98          | ~ (v4_tex_2 @ sk_B_2 @ sk_A)
% 1.74/1.98          | ~ (m1_pre_topc @ sk_B_2 @ sk_A)
% 1.74/1.98          | ~ (v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_2)
% 1.74/1.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 1.74/1.98          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 1.74/1.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.74/1.98          | ~ (v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)
% 1.74/1.98          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 1.74/1.98               (u1_struct_0 @ sk_B_2))
% 1.74/1.98          | ~ (v1_funct_1 @ sk_C_1)
% 1.74/1.98          | ~ (l1_pre_topc @ sk_A)
% 1.74/1.98          | ~ (v3_tdlat_3 @ sk_A)
% 1.74/1.98          | ~ (v2_pre_topc @ sk_A)
% 1.74/1.98          | (v2_struct_0 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['21', '23'])).
% 1.74/1.98  thf('25', plain, ((v4_tex_2 @ sk_B_2 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('26', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('27', plain, ((v3_borsuk_1 @ sk_C_1 @ sk_A @ sk_B_2)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('28', plain, ((v5_pre_topc @ sk_C_1 @ sk_A @ sk_B_2)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('29', plain,
% 1.74/1.98      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('30', plain, ((v1_funct_1 @ sk_C_1)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('32', plain, ((v3_tdlat_3 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('34', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((v2_struct_0 @ sk_B_2)
% 1.74/1.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_2)))
% 1.74/1.98          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98              sk_C_1 @ X0) = (k2_pre_topc @ sk_A @ X0))
% 1.74/1.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.74/1.98          | (v2_struct_0 @ sk_A))),
% 1.74/1.98      inference('demod', [status(thm)],
% 1.74/1.98                ['24', '25', '26', '27', '28', '29', '30', '31', '32', '33'])).
% 1.74/1.98  thf('35', plain,
% 1.74/1.98      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | (v2_struct_0 @ sk_A)
% 1.74/1.98        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 1.74/1.98             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.74/1.98        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98            sk_C_1 @ (k1_tarski @ sk_D))
% 1.74/1.98            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 1.74/1.98        | (v2_struct_0 @ sk_B_2))),
% 1.74/1.98      inference('sup-', [status(thm)], ['20', '34'])).
% 1.74/1.98  thf('36', plain,
% 1.74/1.98      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | (v2_struct_0 @ sk_B_2)
% 1.74/1.98        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98            sk_C_1 @ (k1_tarski @ sk_D))
% 1.74/1.98            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 1.74/1.98        | (v2_struct_0 @ sk_A)
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['19', '35'])).
% 1.74/1.98  thf('37', plain,
% 1.74/1.98      (((v2_struct_0 @ sk_A)
% 1.74/1.98        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98            sk_C_1 @ (k1_tarski @ sk_D))
% 1.74/1.98            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 1.74/1.98        | (v2_struct_0 @ sk_B_2)
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['36'])).
% 1.74/1.98  thf('38', plain,
% 1.74/1.98      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D) = (k1_tarski @ sk_D))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['7', '8'])).
% 1.74/1.98  thf('39', plain,
% 1.74/1.98      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98         sk_C_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D))
% 1.74/1.98         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('40', plain, (((sk_D) = (sk_E))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('41', plain,
% 1.74/1.98      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98         sk_C_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_2) @ sk_D))
% 1.74/1.98         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 1.74/1.98      inference('demod', [status(thm)], ['39', '40'])).
% 1.74/1.98  thf('42', plain,
% 1.74/1.98      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98          sk_C_1 @ (k1_tarski @ sk_D))
% 1.74/1.98          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['38', '41'])).
% 1.74/1.98  thf('43', plain,
% 1.74/1.98      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 1.74/1.98          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | (v2_struct_0 @ sk_B_2)
% 1.74/1.98        | (v2_struct_0 @ sk_A)
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['37', '42'])).
% 1.74/1.98  thf('44', plain,
% 1.74/1.98      (((v2_struct_0 @ sk_A)
% 1.74/1.98        | (v2_struct_0 @ sk_B_2)
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 1.74/1.98            != (k2_pre_topc @ sk_A @ 
% 1.74/1.98                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 1.74/1.98      inference('simplify', [status(thm)], ['43'])).
% 1.74/1.98  thf('45', plain,
% 1.74/1.98      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 1.74/1.98          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | (v2_struct_0 @ sk_B_2)
% 1.74/1.98        | (v2_struct_0 @ sk_A))),
% 1.74/1.98      inference('sup-', [status(thm)], ['5', '44'])).
% 1.74/1.98  thf('46', plain,
% 1.74/1.98      (((v2_struct_0 @ sk_A)
% 1.74/1.98        | (v2_struct_0 @ sk_B_2)
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['45'])).
% 1.74/1.98  thf('47', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(t1_tsep_1, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( l1_pre_topc @ A ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( m1_pre_topc @ B @ A ) =>
% 1.74/1.98           ( m1_subset_1 @
% 1.74/1.98             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.74/1.98  thf('48', plain,
% 1.74/1.98      (![X53 : $i, X54 : $i]:
% 1.74/1.98         (~ (m1_pre_topc @ X53 @ X54)
% 1.74/1.98          | (m1_subset_1 @ (u1_struct_0 @ X53) @ 
% 1.74/1.98             (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.74/1.98          | ~ (l1_pre_topc @ X54))),
% 1.74/1.98      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.74/1.98  thf('49', plain,
% 1.74/1.98      ((~ (l1_pre_topc @ sk_A)
% 1.74/1.98        | (m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.74/1.98      inference('sup-', [status(thm)], ['47', '48'])).
% 1.74/1.98  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('51', plain,
% 1.74/1.98      ((m1_subset_1 @ (u1_struct_0 @ sk_B_2) @ 
% 1.74/1.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.74/1.98      inference('demod', [status(thm)], ['49', '50'])).
% 1.74/1.98  thf(cc1_subset_1, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( v1_xboole_0 @ A ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 1.74/1.98  thf('52', plain,
% 1.74/1.98      (![X37 : $i, X38 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 1.74/1.98          | (v1_xboole_0 @ X37)
% 1.74/1.98          | ~ (v1_xboole_0 @ X38))),
% 1.74/1.98      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.74/1.98  thf('53', plain,
% 1.74/1.98      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['51', '52'])).
% 1.74/1.98  thf('54', plain,
% 1.74/1.98      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))
% 1.74/1.98        | (v2_struct_0 @ sk_B_2)
% 1.74/1.98        | (v2_struct_0 @ sk_A)
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['46', '53'])).
% 1.74/1.98  thf('55', plain,
% 1.74/1.98      (((v2_struct_0 @ sk_A)
% 1.74/1.98        | (v2_struct_0 @ sk_B_2)
% 1.74/1.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_2)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['54'])).
% 1.74/1.98  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('57', plain,
% 1.74/1.98      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_2)) | (v2_struct_0 @ sk_B_2))),
% 1.74/1.98      inference('clc', [status(thm)], ['55', '56'])).
% 1.74/1.98  thf('58', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('59', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_2))),
% 1.74/1.98      inference('clc', [status(thm)], ['57', '58'])).
% 1.74/1.98  thf(t66_tex_2, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 1.74/1.98         ( l1_pre_topc @ A ) ) =>
% 1.74/1.98       ( ?[B:$i]:
% 1.74/1.98         ( ( v3_tex_2 @ B @ A ) & 
% 1.74/1.98           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.74/1.98  thf('60', plain,
% 1.74/1.98      (![X59 : $i]:
% 1.74/1.98         ((m1_subset_1 @ (sk_B_1 @ X59) @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 1.74/1.98          | ~ (l1_pre_topc @ X59)
% 1.74/1.98          | ~ (v3_tdlat_3 @ X59)
% 1.74/1.98          | ~ (v2_pre_topc @ X59)
% 1.74/1.98          | (v2_struct_0 @ X59))),
% 1.74/1.98      inference('cnf', [status(esa)], [t66_tex_2])).
% 1.74/1.98  thf('61', plain,
% 1.74/1.98      (![X37 : $i, X38 : $i]:
% 1.74/1.98         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 1.74/1.98          | (v1_xboole_0 @ X37)
% 1.74/1.98          | ~ (v1_xboole_0 @ X38))),
% 1.74/1.98      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.74/1.98  thf('62', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((v2_struct_0 @ X0)
% 1.74/1.98          | ~ (v2_pre_topc @ X0)
% 1.74/1.98          | ~ (v3_tdlat_3 @ X0)
% 1.74/1.98          | ~ (l1_pre_topc @ X0)
% 1.74/1.98          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.74/1.98          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['60', '61'])).
% 1.74/1.98  thf('63', plain,
% 1.74/1.98      (((v1_xboole_0 @ (sk_B_1 @ sk_B_2))
% 1.74/1.98        | ~ (l1_pre_topc @ sk_B_2)
% 1.74/1.98        | ~ (v3_tdlat_3 @ sk_B_2)
% 1.74/1.98        | ~ (v2_pre_topc @ sk_B_2)
% 1.74/1.98        | (v2_struct_0 @ sk_B_2))),
% 1.74/1.98      inference('sup-', [status(thm)], ['59', '62'])).
% 1.74/1.98  thf('64', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(dt_m1_pre_topc, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( l1_pre_topc @ A ) =>
% 1.74/1.98       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.74/1.98  thf('65', plain,
% 1.74/1.98      (![X44 : $i, X45 : $i]:
% 1.74/1.98         (~ (m1_pre_topc @ X44 @ X45)
% 1.74/1.98          | (l1_pre_topc @ X44)
% 1.74/1.98          | ~ (l1_pre_topc @ X45))),
% 1.74/1.98      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.74/1.98  thf('66', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_2))),
% 1.74/1.98      inference('sup-', [status(thm)], ['64', '65'])).
% 1.74/1.98  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('68', plain, ((l1_pre_topc @ sk_B_2)),
% 1.74/1.98      inference('demod', [status(thm)], ['66', '67'])).
% 1.74/1.98  thf('69', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(cc9_tdlat_3, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 1.74/1.98         ( l1_pre_topc @ A ) ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( m1_pre_topc @ B @ A ) =>
% 1.74/1.98           ( ( ~( v2_struct_0 @ B ) ) =>
% 1.74/1.98             ( ( ~( v2_struct_0 @ B ) ) & ( v3_tdlat_3 @ B ) ) ) ) ) ))).
% 1.74/1.98  thf('70', plain,
% 1.74/1.98      (![X55 : $i, X56 : $i]:
% 1.74/1.98         (~ (m1_pre_topc @ X55 @ X56)
% 1.74/1.98          | (v3_tdlat_3 @ X55)
% 1.74/1.98          | (v2_struct_0 @ X55)
% 1.74/1.98          | ~ (l1_pre_topc @ X56)
% 1.74/1.98          | ~ (v3_tdlat_3 @ X56)
% 1.74/1.98          | ~ (v2_pre_topc @ X56)
% 1.74/1.98          | (v2_struct_0 @ X56))),
% 1.74/1.98      inference('cnf', [status(esa)], [cc9_tdlat_3])).
% 1.74/1.98  thf('71', plain,
% 1.74/1.98      (((v2_struct_0 @ sk_A)
% 1.74/1.98        | ~ (v2_pre_topc @ sk_A)
% 1.74/1.98        | ~ (v3_tdlat_3 @ sk_A)
% 1.74/1.98        | ~ (l1_pre_topc @ sk_A)
% 1.74/1.98        | (v2_struct_0 @ sk_B_2)
% 1.74/1.98        | (v3_tdlat_3 @ sk_B_2))),
% 1.74/1.98      inference('sup-', [status(thm)], ['69', '70'])).
% 1.74/1.98  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('73', plain, ((v3_tdlat_3 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('75', plain,
% 1.74/1.98      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_2) | (v3_tdlat_3 @ sk_B_2))),
% 1.74/1.98      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 1.74/1.98  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('77', plain, (((v3_tdlat_3 @ sk_B_2) | (v2_struct_0 @ sk_B_2))),
% 1.74/1.98      inference('clc', [status(thm)], ['75', '76'])).
% 1.74/1.98  thf('78', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('79', plain, ((v3_tdlat_3 @ sk_B_2)),
% 1.74/1.98      inference('clc', [status(thm)], ['77', '78'])).
% 1.74/1.98  thf('80', plain, ((m1_pre_topc @ sk_B_2 @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(cc1_pre_topc, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.98       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.74/1.98  thf('81', plain,
% 1.74/1.98      (![X42 : $i, X43 : $i]:
% 1.74/1.98         (~ (m1_pre_topc @ X42 @ X43)
% 1.74/1.98          | (v2_pre_topc @ X42)
% 1.74/1.98          | ~ (l1_pre_topc @ X43)
% 1.74/1.98          | ~ (v2_pre_topc @ X43))),
% 1.74/1.98      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.74/1.98  thf('82', plain,
% 1.74/1.98      ((~ (v2_pre_topc @ sk_A)
% 1.74/1.98        | ~ (l1_pre_topc @ sk_A)
% 1.74/1.98        | (v2_pre_topc @ sk_B_2))),
% 1.74/1.98      inference('sup-', [status(thm)], ['80', '81'])).
% 1.74/1.98  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('85', plain, ((v2_pre_topc @ sk_B_2)),
% 1.74/1.98      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.74/1.98  thf('86', plain,
% 1.74/1.98      (((v1_xboole_0 @ (sk_B_1 @ sk_B_2)) | (v2_struct_0 @ sk_B_2))),
% 1.74/1.98      inference('demod', [status(thm)], ['63', '68', '79', '85'])).
% 1.74/1.98  thf('87', plain, (~ (v2_struct_0 @ sk_B_2)),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('88', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_B_2))),
% 1.74/1.98      inference('clc', [status(thm)], ['86', '87'])).
% 1.74/1.98  thf('89', plain,
% 1.74/1.98      (![X59 : $i]:
% 1.74/1.98         ((v3_tex_2 @ (sk_B_1 @ X59) @ X59)
% 1.74/1.98          | ~ (l1_pre_topc @ X59)
% 1.74/1.98          | ~ (v3_tdlat_3 @ X59)
% 1.74/1.98          | ~ (v2_pre_topc @ X59)
% 1.74/1.98          | (v2_struct_0 @ X59))),
% 1.74/1.98      inference('cnf', [status(esa)], [t66_tex_2])).
% 1.74/1.98  thf(d3_tarski, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( r1_tarski @ A @ B ) <=>
% 1.74/1.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.74/1.98  thf('90', plain,
% 1.74/1.98      (![X4 : $i, X6 : $i]:
% 1.74/1.98         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.74/1.98      inference('cnf', [status(esa)], [d3_tarski])).
% 1.74/1.98  thf(d1_xboole_0, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.74/1.98  thf('91', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.74/1.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.74/1.98  thf('92', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['90', '91'])).
% 1.74/1.98  thf(t3_subset, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.74/1.98  thf('93', plain,
% 1.74/1.98      (![X39 : $i, X41 : $i]:
% 1.74/1.98         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 1.74/1.98      inference('cnf', [status(esa)], [t3_subset])).
% 1.74/1.98  thf('94', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['92', '93'])).
% 1.74/1.98  thf(t46_tex_2, axiom,
% 1.74/1.98    (![A:$i]:
% 1.74/1.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.74/1.98       ( ![B:$i]:
% 1.74/1.98         ( ( ( v1_xboole_0 @ B ) & 
% 1.74/1.98             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.74/1.98           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.74/1.98  thf('95', plain,
% 1.74/1.98      (![X57 : $i, X58 : $i]:
% 1.74/1.98         (~ (v1_xboole_0 @ X57)
% 1.74/1.98          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 1.74/1.98          | ~ (v3_tex_2 @ X57 @ X58)
% 1.74/1.98          | ~ (l1_pre_topc @ X58)
% 1.74/1.98          | ~ (v2_pre_topc @ X58)
% 1.74/1.98          | (v2_struct_0 @ X58))),
% 1.74/1.98      inference('cnf', [status(esa)], [t46_tex_2])).
% 1.74/1.98  thf('96', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (v1_xboole_0 @ X1)
% 1.74/1.98          | (v2_struct_0 @ X0)
% 1.74/1.98          | ~ (v2_pre_topc @ X0)
% 1.74/1.98          | ~ (l1_pre_topc @ X0)
% 1.74/1.98          | ~ (v3_tex_2 @ X1 @ X0)
% 1.74/1.98          | ~ (v1_xboole_0 @ X1))),
% 1.74/1.98      inference('sup-', [status(thm)], ['94', '95'])).
% 1.74/1.98  thf('97', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (v3_tex_2 @ X1 @ X0)
% 1.74/1.98          | ~ (l1_pre_topc @ X0)
% 1.74/1.98          | ~ (v2_pre_topc @ X0)
% 1.74/1.98          | (v2_struct_0 @ X0)
% 1.74/1.98          | ~ (v1_xboole_0 @ X1))),
% 1.74/1.98      inference('simplify', [status(thm)], ['96'])).
% 1.74/1.98  thf('98', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((v2_struct_0 @ X0)
% 1.74/1.98          | ~ (v2_pre_topc @ X0)
% 1.74/1.98          | ~ (v3_tdlat_3 @ X0)
% 1.74/1.98          | ~ (l1_pre_topc @ X0)
% 1.74/1.98          | ~ (v1_xboole_0 @ (sk_B_1 @ X0))
% 1.74/1.98          | (v2_struct_0 @ X0)
% 1.74/1.98          | ~ (v2_pre_topc @ X0)
% 1.74/1.98          | ~ (l1_pre_topc @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['89', '97'])).
% 1.74/1.98  thf('99', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (~ (v1_xboole_0 @ (sk_B_1 @ X0))
% 1.74/1.98          | ~ (l1_pre_topc @ X0)
% 1.74/1.98          | ~ (v3_tdlat_3 @ X0)
% 1.74/1.98          | ~ (v2_pre_topc @ X0)
% 1.74/1.98          | (v2_struct_0 @ X0))),
% 1.74/1.98      inference('simplify', [status(thm)], ['98'])).
% 1.74/1.98  thf('100', plain,
% 1.74/1.98      (((v2_struct_0 @ sk_B_2)
% 1.74/1.98        | ~ (v2_pre_topc @ sk_B_2)
% 1.74/1.98        | ~ (v3_tdlat_3 @ sk_B_2)
% 1.74/1.98        | ~ (l1_pre_topc @ sk_B_2))),
% 1.74/1.98      inference('sup-', [status(thm)], ['88', '99'])).
% 1.74/1.98  thf('101', plain, ((v2_pre_topc @ sk_B_2)),
% 1.74/1.98      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.74/1.98  thf('102', plain, ((v3_tdlat_3 @ sk_B_2)),
% 1.74/1.98      inference('clc', [status(thm)], ['77', '78'])).
% 1.74/1.98  thf('103', plain, ((l1_pre_topc @ sk_B_2)),
% 1.74/1.98      inference('demod', [status(thm)], ['66', '67'])).
% 1.74/1.98  thf('104', plain, ((v2_struct_0 @ sk_B_2)),
% 1.74/1.98      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 1.74/1.98  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 1.74/1.98  
% 1.74/1.98  % SZS output end Refutation
% 1.74/1.98  
% 1.74/1.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
