%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4E22NuBS7r

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 194 expanded)
%              Number of leaves         :   37 (  73 expanded)
%              Depth                    :   23
%              Number of atoms          : 1111 (5347 expanded)
%              Number of equality atoms :   35 ( 162 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_domain_1_type,type,(
    k7_domain_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

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
    ! [X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ X43 )
      | ( ( k6_domain_1 @ X43 @ X44 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k7_domain_1 @ A @ B @ C )
        = ( k2_tarski @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ X46 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ X46 )
      | ( ( k7_domain_1 @ X46 @ X45 @ X47 )
        = ( k2_tarski @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_domain_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 )
        = ( k2_tarski @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D )
      = ( k2_tarski @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D )
      = ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A )
        & ( m1_subset_1 @ C @ A ) )
     => ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ X41 )
      | ( m1_subset_1 @ ( k7_domain_1 @ X41 @ X40 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_domain_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D )
      = ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k7_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('31',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( v2_struct_0 @ X50 )
      | ~ ( v4_tex_2 @ X50 @ X51 )
      | ~ ( m1_pre_topc @ X50 @ X51 )
      | ~ ( v3_borsuk_1 @ X52 @ X51 @ X50 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( X53 != X54 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) @ X52 @ X53 )
        = ( k2_pre_topc @ X51 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( v5_pre_topc @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_2 @ X52 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v3_tdlat_3 @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ( v2_struct_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('32',plain,(
    ! [X50: $i,X51: $i,X52: $i,X54: $i] :
      ( ( v2_struct_0 @ X51 )
      | ~ ( v2_pre_topc @ X51 )
      | ~ ( v3_tdlat_3 @ X51 )
      | ~ ( l1_pre_topc @ X51 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) )
      | ~ ( v5_pre_topc @ X52 @ X51 @ X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X51 ) @ ( u1_struct_0 @ X50 ) @ X52 @ X54 )
        = ( k2_pre_topc @ X51 @ X54 ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v3_borsuk_1 @ X52 @ X51 @ X50 )
      | ~ ( m1_pre_topc @ X50 @ X51 )
      | ~ ( v4_tex_2 @ X50 @ X51 )
      | ( v2_struct_0 @ X50 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_tex_2 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35','36','37','38','39','40','41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ X43 )
      | ( ( k6_domain_1 @ X43 @ X44 )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('49',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('58',plain,(
    ! [X36: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('61',plain,(
    ! [X33: $i] :
      ( ( l1_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X36: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('72',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X34 @ X35 )
      | ( l1_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X33: $i] :
      ( ( l1_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['70','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4E22NuBS7r
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:09:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 140 iterations in 0.090s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.22/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.56  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.22/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.56  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.22/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.56  thf(k7_domain_1_type, type, k7_domain_1: $i > $i > $i > $i).
% 0.22/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.56  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.22/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.56  thf(t77_tex_2, conjecture,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.22/0.56         ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.22/0.56             ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.56           ( ![C:$i]:
% 0.22/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.56                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.22/0.56                 ( m1_subset_1 @
% 0.22/0.56                   C @ 
% 0.22/0.56                   ( k1_zfmisc_1 @
% 0.22/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.56               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.22/0.56                 ( ![D:$i]:
% 0.22/0.56                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.56                     ( ![E:$i]:
% 0.22/0.56                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.56                         ( ( ( D ) = ( E ) ) =>
% 0.22/0.56                           ( ( k8_relset_1 @
% 0.22/0.56                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.56                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.22/0.56                             ( k2_pre_topc @
% 0.22/0.56                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i]:
% 0.22/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.56            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.56          ( ![B:$i]:
% 0.22/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.22/0.56                ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.56              ( ![C:$i]:
% 0.22/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.56                    ( v1_funct_2 @
% 0.22/0.56                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.56                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.22/0.56                    ( m1_subset_1 @
% 0.22/0.56                      C @ 
% 0.22/0.56                      ( k1_zfmisc_1 @
% 0.22/0.56                        ( k2_zfmisc_1 @
% 0.22/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.56                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.22/0.56                    ( ![D:$i]:
% 0.22/0.56                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.56                        ( ![E:$i]:
% 0.22/0.56                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.56                            ( ( ( D ) = ( E ) ) =>
% 0.22/0.56                              ( ( k8_relset_1 @
% 0.22/0.56                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.22/0.56                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.22/0.56                                ( k2_pre_topc @
% 0.22/0.56                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.22/0.56  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('1', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('2', plain, (((sk_D) = (sk_E))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (![X43 : $i, X44 : $i]:
% 0.22/0.56         ((v1_xboole_0 @ X43)
% 0.22/0.56          | ~ (m1_subset_1 @ X44 @ X43)
% 0.22/0.56          | ((k6_domain_1 @ X43 @ X44) = (k1_tarski @ X44)))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.56  thf('6', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('7', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(redefinition_k7_domain_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) & 
% 0.22/0.56         ( m1_subset_1 @ C @ A ) ) =>
% 0.22/0.56       ( ( k7_domain_1 @ A @ B @ C ) = ( k2_tarski @ B @ C ) ) ))).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X45 @ X46)
% 0.22/0.56          | (v1_xboole_0 @ X46)
% 0.22/0.56          | ~ (m1_subset_1 @ X47 @ X46)
% 0.22/0.56          | ((k7_domain_1 @ X46 @ X45 @ X47) = (k2_tarski @ X45 @ X47)))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k7_domain_1])).
% 0.22/0.56  thf('9', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ X0)
% 0.22/0.56            = (k2_tarski @ sk_D @ X0))
% 0.22/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | ((k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)
% 0.22/0.56            = (k2_tarski @ sk_D @ sk_D)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.56  thf(t69_enumset1, axiom,
% 0.22/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.56  thf('11', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | ((k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)
% 0.22/0.56            = (k1_tarski @ sk_D)))),
% 0.22/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.56  thf('13', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('14', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('15', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(dt_k7_domain_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) & 
% 0.22/0.56         ( m1_subset_1 @ C @ A ) ) =>
% 0.22/0.56       ( m1_subset_1 @ ( k7_domain_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.56  thf('16', plain,
% 0.22/0.56      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ X40 @ X41)
% 0.22/0.56          | (v1_xboole_0 @ X41)
% 0.22/0.56          | ~ (m1_subset_1 @ X42 @ X41)
% 0.22/0.56          | (m1_subset_1 @ (k7_domain_1 @ X41 @ X40 @ X42) @ 
% 0.22/0.56             (k1_zfmisc_1 @ X41)))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_k7_domain_1])).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ X0) @ 
% 0.22/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.22/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.56  thf(t39_pre_topc, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.56           ( ![C:$i]:
% 0.22/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.56               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.22/0.56         (~ (m1_pre_topc @ X37 @ X38)
% 0.22/0.56          | (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.22/0.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.22/0.56          | ~ (l1_pre_topc @ X38))),
% 0.22/0.56      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56          | ~ (l1_pre_topc @ X0)
% 0.22/0.56          | (m1_subset_1 @ 
% 0.22/0.56             (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.22/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.56          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.22/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['13', '20'])).
% 0.22/0.56  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('23', plain,
% 0.22/0.56      (((m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.22/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('sup+', [status(thm)], ['12', '23'])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | ((k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D)
% 0.22/0.56            = (k1_tarski @ sk_D)))),
% 0.22/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (m1_subset_1 @ (k7_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D @ sk_D) @ 
% 0.22/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.56  thf('30', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_C @ 
% 0.22/0.56        (k1_zfmisc_1 @ 
% 0.22/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(t76_tex_2, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.22/0.56         ( l1_pre_topc @ A ) ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.22/0.56             ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.56           ( ![C:$i]:
% 0.22/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.56                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.22/0.56                 ( m1_subset_1 @
% 0.22/0.56                   C @ 
% 0.22/0.56                   ( k1_zfmisc_1 @
% 0.22/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.56               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.22/0.56                 ( ![D:$i]:
% 0.22/0.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.56                     ( ![E:$i]:
% 0.22/0.56                       ( ( m1_subset_1 @
% 0.22/0.56                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.56                         ( ( ( D ) = ( E ) ) =>
% 0.22/0.56                           ( ( k8_relset_1 @
% 0.22/0.56                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.56                               D ) =
% 0.22/0.56                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.22/0.56         ((v2_struct_0 @ X50)
% 0.22/0.56          | ~ (v4_tex_2 @ X50 @ X51)
% 0.22/0.56          | ~ (m1_pre_topc @ X50 @ X51)
% 0.22/0.56          | ~ (v3_borsuk_1 @ X52 @ X51 @ X50)
% 0.22/0.56          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.22/0.56          | ((X53) != (X54))
% 0.22/0.56          | ((k8_relset_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50) @ X52 @ 
% 0.22/0.56              X53) = (k2_pre_topc @ X51 @ X54))
% 0.22/0.56          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.22/0.56          | ~ (m1_subset_1 @ X52 @ 
% 0.22/0.56               (k1_zfmisc_1 @ 
% 0.22/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))))
% 0.22/0.56          | ~ (v5_pre_topc @ X52 @ X51 @ X50)
% 0.22/0.56          | ~ (v1_funct_2 @ X52 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))
% 0.22/0.56          | ~ (v1_funct_1 @ X52)
% 0.22/0.56          | ~ (l1_pre_topc @ X51)
% 0.22/0.56          | ~ (v3_tdlat_3 @ X51)
% 0.22/0.56          | ~ (v2_pre_topc @ X51)
% 0.22/0.56          | (v2_struct_0 @ X51))),
% 0.22/0.56      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.22/0.56  thf('32', plain,
% 0.22/0.56      (![X50 : $i, X51 : $i, X52 : $i, X54 : $i]:
% 0.22/0.56         ((v2_struct_0 @ X51)
% 0.22/0.56          | ~ (v2_pre_topc @ X51)
% 0.22/0.56          | ~ (v3_tdlat_3 @ X51)
% 0.22/0.56          | ~ (l1_pre_topc @ X51)
% 0.22/0.56          | ~ (v1_funct_1 @ X52)
% 0.22/0.56          | ~ (v1_funct_2 @ X52 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))
% 0.22/0.56          | ~ (v5_pre_topc @ X52 @ X51 @ X50)
% 0.22/0.56          | ~ (m1_subset_1 @ X52 @ 
% 0.22/0.56               (k1_zfmisc_1 @ 
% 0.22/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50))))
% 0.22/0.56          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.22/0.56          | ((k8_relset_1 @ (u1_struct_0 @ X51) @ (u1_struct_0 @ X50) @ X52 @ 
% 0.22/0.56              X54) = (k2_pre_topc @ X51 @ X54))
% 0.22/0.56          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.22/0.56          | ~ (v3_borsuk_1 @ X52 @ X51 @ X50)
% 0.22/0.56          | ~ (m1_pre_topc @ X50 @ X51)
% 0.22/0.56          | ~ (v4_tex_2 @ X50 @ X51)
% 0.22/0.56          | (v2_struct_0 @ X50))),
% 0.22/0.56      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.56  thf('33', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v2_struct_0 @ sk_B)
% 0.22/0.56          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.22/0.56          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.22/0.56          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B)
% 0.22/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.56          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.56              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.22/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.56          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.22/0.56          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.56          | ~ (v3_tdlat_3 @ sk_A)
% 0.22/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.56          | (v2_struct_0 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['30', '32'])).
% 0.22/0.56  thf('34', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('36', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('37', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('41', plain, ((v3_tdlat_3 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('43', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v2_struct_0 @ sk_B)
% 0.22/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.56          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.56              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.22/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.56          | (v2_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)],
% 0.22/0.56                ['33', '34', '35', '36', '37', '38', '39', '40', '41', '42'])).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.22/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.56        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.56            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.22/0.56        | (v2_struct_0 @ sk_B))),
% 0.22/0.56      inference('sup-', [status(thm)], ['29', '43'])).
% 0.22/0.56  thf('45', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (v2_struct_0 @ sk_B)
% 0.22/0.56        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.56            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['25', '44'])).
% 0.22/0.56  thf('46', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.56            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.22/0.56        | (v2_struct_0 @ sk_B)
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.56  thf('47', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('48', plain,
% 0.22/0.56      (![X43 : $i, X44 : $i]:
% 0.22/0.56         ((v1_xboole_0 @ X43)
% 0.22/0.56          | ~ (m1_subset_1 @ X44 @ X43)
% 0.22/0.56          | ((k6_domain_1 @ X43 @ X44) = (k1_tarski @ X44)))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.56  thf('49', plain,
% 0.22/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.56  thf('50', plain,
% 0.22/0.56      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.22/0.56         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('51', plain, (((sk_D) = (sk_E))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('52', plain,
% 0.22/0.56      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.56         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.22/0.56         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.22/0.56      inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.56  thf('53', plain,
% 0.22/0.56      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.56          (k1_tarski @ sk_D))
% 0.22/0.56          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['49', '52'])).
% 0.22/0.56  thf('54', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.22/0.56          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (v2_struct_0 @ sk_B)
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['46', '53'])).
% 0.22/0.56  thf('55', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | (v2_struct_0 @ sk_B)
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.22/0.56            != (k2_pre_topc @ sk_A @ 
% 0.22/0.56                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.22/0.56      inference('simplify', [status(thm)], ['54'])).
% 0.22/0.56  thf('56', plain,
% 0.22/0.56      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.22/0.56          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (v2_struct_0 @ sk_B)
% 0.22/0.56        | (v2_struct_0 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['5', '55'])).
% 0.22/0.56  thf('57', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | (v2_struct_0 @ sk_B)
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.56  thf(fc2_struct_0, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.56  thf('58', plain,
% 0.22/0.56      (![X36 : $i]:
% 0.22/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X36))
% 0.22/0.56          | ~ (l1_struct_0 @ X36)
% 0.22/0.56          | (v2_struct_0 @ X36))),
% 0.22/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.56  thf('59', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (v2_struct_0 @ sk_B)
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.56  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(dt_l1_pre_topc, axiom,
% 0.22/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.56  thf('61', plain,
% 0.22/0.56      (![X33 : $i]: ((l1_struct_0 @ X33) | ~ (l1_pre_topc @ X33))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.56  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.56  thf('63', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.56        | (v2_struct_0 @ sk_B)
% 0.22/0.56        | (v2_struct_0 @ sk_A)
% 0.22/0.56        | (v2_struct_0 @ sk_A))),
% 0.22/0.56      inference('demod', [status(thm)], ['59', '62'])).
% 0.22/0.56  thf('64', plain,
% 0.22/0.56      (((v2_struct_0 @ sk_A)
% 0.22/0.56        | (v2_struct_0 @ sk_B)
% 0.22/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['63'])).
% 0.22/0.56  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('66', plain,
% 0.22/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.22/0.56      inference('clc', [status(thm)], ['64', '65'])).
% 0.22/0.56  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('68', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.22/0.56      inference('clc', [status(thm)], ['66', '67'])).
% 0.22/0.56  thf('69', plain,
% 0.22/0.56      (![X36 : $i]:
% 0.22/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X36))
% 0.22/0.56          | ~ (l1_struct_0 @ X36)
% 0.22/0.56          | (v2_struct_0 @ X36))),
% 0.22/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.56  thf('70', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.56  thf('71', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(dt_m1_pre_topc, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( l1_pre_topc @ A ) =>
% 0.22/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.56  thf('72', plain,
% 0.22/0.56      (![X34 : $i, X35 : $i]:
% 0.22/0.56         (~ (m1_pre_topc @ X34 @ X35)
% 0.22/0.56          | (l1_pre_topc @ X34)
% 0.22/0.56          | ~ (l1_pre_topc @ X35))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.56  thf('73', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.56  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.22/0.56  thf('76', plain,
% 0.22/0.56      (![X33 : $i]: ((l1_struct_0 @ X33) | ~ (l1_pre_topc @ X33))),
% 0.22/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.56  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.56      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.56  thf('78', plain, ((v2_struct_0 @ sk_B)),
% 0.22/0.56      inference('demod', [status(thm)], ['70', '77'])).
% 0.22/0.56  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
